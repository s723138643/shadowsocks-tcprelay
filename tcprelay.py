#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Copyright 2015 clowwindy
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

from __future__ import absolute_import, division, print_function, \
    with_statement

import time
import socket
import errno
import struct
import logging
import random
import heapq

from collections import deque

from shadowsocks import encrypt, eventloop, shell, common
from shadowsocks.common import parse_header

# we clear at most TIMEOUTS_CLEAN_SIZE timeouts each time
TIMEOUTS_CLEAN_SIZE = 512

MSG_FASTOPEN = 0x20000000

# SOCKS METHOD definition
METHOD_NOAUTH = 0

# SOCKS command definition
CMD_CONNECT = 1
CMD_BIND = 2
CMD_UDP_ASSOCIATE = 3

# for each opening port, we have a TCP Relay

# for each connection, we have a TCP Relay Handler to handle the connection

# for each handler, we have 2 sockets:
#    local:   connected to the client
#    remote:  connected to remote server

# for each handler, it could be at one of several stages:

# as sslocal:
# stage 0 auth METHOD received from local, reply with selection message
# stage 1 addr received from local, query DNS for remote
# stage 2 UDP assoc
# stage 3 DNS resolved, connect to remote
# stage 4 still connecting, more data from local received
# stage 5 remote connected, piping local and remote

# as ssserver:
# stage 0 just jump to stage 1
# stage 1 addr received from local, query DNS for remote
# stage 3 DNS resolved, connect to remote
# stage 4 still connecting, more data from local received
# stage 5 remote connected, piping local and remote

STAGE_INIT = 0
STAGE_ADDR = 1
STAGE_UDP_ASSOC = 2
STAGE_DNS = 3
STAGE_CONNECTING = 4
STAGE_STREAM = 5
STAGE_WAIT_CLOSE = 6
STAGE_WAIT_DESTROY = 7

# for each stream, it's waiting for reading, or writing, or both
WAIT_STATUS_INIT = eventloop.POLL_NULL
WAIT_STATUS_READING = eventloop.POLL_IN
WAIT_STATUS_WRITING = eventloop.POLL_OUT
WAIT_STATUS_READWRITING = WAIT_STATUS_READING | WAIT_STATUS_WRITING

BUF_SIZE = 16 * 1024


class BaseRelay:

    def __init__(self):
        self._closed = False
        self._handlers = []
        self._eventloop = False

    def add_to_loop(self, loop):
        if self._eventloop:
            raise Exception('already add to loop')
        if self._closed:
            raise Exception('already closed')
        self._eventloop = loop
        self._eventloop.add(self._listen_socket,
                            eventloop.POLL_IN,
                            self)
        self._eventloop.add_periodic(self.handle_periodic)

    def remove_handler(self, handler):
        def heap_remove_up(l, index, item):
            while index > 0:
                parent = (index - 1) // 2
                if item < l[parent]:
                    l[index] = l[parent]
                    index = parent
                else:
                    l[index] = item
                    break
            else:
                l[0] = item

        def heap_remove_down(l, index, item):
            length = len(l)
            while index < length:
                left = index * 2 + 1
                right = left + 1

                mins = None
                smaller = item
                if left < length and l[left] < smaller:
                    mins = left
                    smaller = l[left]
                if right < length and l[right] < smaller:
                    mins = right

                if mins:  # item is not the smallest one
                    l[index] = l[mins]
                    index = mins
                else:
                    # left and right out of range
                    # or item is the smallest one
                    l[index] = item
                    break

        if not self._handlers:
            return

        if self._handlers[-1] == handler:
            self._handlers.pop()
        elif self._handlers[0] == handler:
            last = self._handlers.pop()
            heap_remove_down(self._handlers, 0, last)
        else:
            index = self._handlers.index(handler)
            last = self._handlers.pop()
            parent = (index - 1) // 2
            if self._handlers[parent] < last:
                heap_remove_down(self._handlers, index, last)
            else:
                heap_remove_up(self._handlers, index, last)

    def handle_event(self, sock, fd, event):
        if sock == self._listen_socket:
            self._accept_connet()

    def handle_periodic(self):
        if self._closed:
            if self._listen_socket:
                self._eventloop.remove(self._listen_socket)
                self._listen_socket.close()
                self._listen_socket = None
                logging.info('closed TCP port %d', self._listen_port)
            if not self._handlers:
                logging.info('stopping')
                self._eventloop.stop()
        self._sweep_timeout()

    def _update_activity(self, handler):
        def heapify(l, index):
            length = len(l)
            while index < length:
                left = 2 * index + 1
                right = left + 1

                min_index = index
                if left < length and l[left] < l[min_index]:
                    min_index = left
                if right < length and l[right] < l[min_index]:
                    min_index = right

                if min_index != index:
                    l[min_index], l[index] = l[index], l[min_index]
                    index = min_index
                else:
                    break

        handler.last_activity = time.time()
        index = self._handlers.index(handler)
        heapify(self._handlers, index)

    def _sweep_timeout(self):
        if self._handlers:
            logging.info('sweeping timeouts, total handlers:{}'
                         .format(len(self._handlers)))
            now = time.time()
            count = 0
            while self._handlers:
                handler = self._handlers[0]
                if now-handler.last_activity < self._timeout:
                    break
                if handler.is_destroyed():
                    heapq.heappop(self._handlers)
                    continue    # handler were destroyed early

                stream = None
                if handler._mapper['remote'].sock:
                    stream = 'remote'
                elif handler._mapper['local'].sock:
                    stream = 'local'
                if stream:
                    logging.warn('timeout: {}:{}'
                                 .format(handler._mapper[stream].addr,
                                         handler._mapper[stream].port))
                else:
                    logging.warn('unexcepted error, remote '
                                 'and local all closed')
                handler.destroy()
                count += 1
            if count > 0:
                logging.info('{} handler had swept'.format(count))

    def _accept(self, Handler):
        conn, address = self._listen_socket.accept()
        logging.debug('fd[{}] accept connect {}:{}'
                      .format(self._listen_socket.fileno(),
                              address[0], address[1]))
        handler = Handler(self, conn, self._eventloop,
                          self._config, self._dns_resolver)
        heapq.heappush(self._handlers, handler)
        conn.setsockopt(socket.SOL_TCP, socket.TCP_NODELAY, 1)
        conn.setblocking(False)
        self._eventloop.add(conn, eventloop.POLL_IN, handler)

    def _create_socket(self, addr, port):
        addrs = socket.getaddrinfo(addr, port, 0,
                                   socket.SOCK_STREAM, socket.SOL_TCP)
        if len(addrs) == 0:
            raise Exception('Can\'t get addrinfo for %s:%d' % (addr, port))
        af, stype, proto, _, sa = addrs[0]

        listen_sock = socket.socket(af, stype, proto)
        listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listen_sock.bind(sa)
        listen_sock.listen(1024)
        listen_sock.setblocking(False)

        return listen_sock

    def close(self, next_tick=False):
        logging.info('TCPRelay closing ...')
        self._closed = True
        if not next_tick:
            if self._eventloop:
                self._eventloop.remove_periodic(self.handle_periodic)
                self._eventloop.remove(self._listen_socket)
            self._listen_socket.close()
            for handler in self._handlers.copy():
                handler.destroy()


class LocalTCPRelay(BaseRelay):
    def __init__(self, config, dns_resolver, stat_callback=None):
        super(LocalTCPRelay, self).__init__()
        self._config = config
        self._dns_resolver = dns_resolver
        self._timeout = config['timeout']

        listen_addr = config['local_address']
        listen_port = config['local_port']

        self._listen_socket = self._create_socket(listen_addr, listen_port)
        self._listen_port = listen_port
        self._stat_callback = stat_callback

    def _accept_connet(self):
        self._accept(LocalTCPRelayHandler)


class RemoteTCPRelay(BaseRelay):
    def __init__(self, config, dns_resolver, stat_callback=None):
        super(RemoteTCPRelay, self).__init__()
        self._config = config
        self._dns_resolver = dns_resolver
        self._stat_callback = stat_callback
        self._timeout = config['timeout']
        listen_addr = config['server']
        listen_port = config['server_port']

        self._fastopen = config['fast_open']

        self._listen_socket = self._create_socket(listen_addr, listen_port)
        if self._fastopen:
            logging.info('using fast open')
            try:
                self._listen_socket.setsockopt(socket.SOL_TCP, 23, 5)
            except socket.err:
                logging.warn('fast open is not available')
                self._fastopen = False
        self._listen_port = listen_port
        self._stat_callback = stat_callback

    def _accept_connet(self):
        self._accept(RemoteTCPRelayHandler)


# TCPRelay factory create relay arccording to is_local flag
def TCPRelay(config, dns_resolver, is_local, stat_callback=None):
    if is_local:
        return LocalTCPRelay(config, dns_resolver, stat_callback)
    else:
        return RemoteTCPRelay(config, dns_resolver, stat_callback)


class Mapper:
    __slots__ = ['sock', '_fd', 'stream', '_addr', '_port',
                 'read_buffer', 'write_buffer', 'closed']

    def __init__(self, sock=None, stream=None):
        self.sock = sock if sock else None
        self._fd = sock.fileno() if sock else None
        self.stream = WAIT_STATUS_READING if not stream else stream
        self.read_buffer = b''
        self.write_buffer = deque()
        self._addr = None
        self._port = None
        self.closed = False

    @property
    def addr(self):
        if self.sock and not self._addr:
            self._addr, self._port, *_ = self.sock.getpeername()
        return self._addr

    @addr.setter
    def addr(self, value):
        self._addr = value

    @property
    def port(self):
        if self.sock and not self._port:
            self._addr, self._port, *_ = self.sock.getpeername()
        return self._port

    @port.setter
    def port(self, value):
        self._port = value

    @property
    def fd(self):
        if self.sock and not self._fd:
            self._fd = self.sock.fileno()
        return self._fd


class BaseHandler:

    def __init__(self):
        self.last_activity = time.time()
        self._destroyed = False

    def __lt__(self, other):
        return self.last_activity < other.last_activity

    def __le__(self, other):
        return self.last_activity <= other.last_activity

    def __hash__(self):
        return id(self)

    def is_destroyed(self):
        return self._destroyed is True

    def is_closed(self, stream):
        return self._mapper[stream].closed is True

    def _create_remote_socket(self, ip, port):
        addrs = socket.getaddrinfo(ip, port, 0,
                                   socket.SOCK_STREAM,
                                   socket.SOL_TCP)
        if len(addrs) == 0:
            raise Exception("getaddrinfo failed for %s:%d" % (ip, port))
        af, socktype, proto, canonname, sa = addrs[0]
        if common.to_str(sa[0]) in self._forbidden_iplist:
            raise Exception('IP %s is in forbidden list, reject'
                            % common.to_str(sa[0]))
        sock = socket.socket(af, socktype, proto)
        sock.setblocking(False)
        sock.setsockopt(socket.SOL_TCP, socket.TCP_NODELAY, 1)
        return sock

    def _handle_write(self, stream):
        sock = self._mapper[stream].sock
        buf = self._mapper[stream].write_buffer
        try:
            for i in range(10):
                if not buf:
                    return True
                data = buf[0]
                l = sock.send(data)
                if len(data) == l:
                    del buf[0]
                else:
                    buf[0] = data[l:]
        except (IOError, OSError) as e:
            err = eventloop.errno_from_exception(e)
            # ignore EAGAIN and EWOULDBLOCK errors, reraise other errors
            # these errors will be dealed by up level
            if err not in (errno.EAGAIN, errno.EWOULDBLOCK):
                raise
            else:
                return False
        return False

    def _handle_read(self, stream):
        sock = self._mapper[stream].sock
        readed = self._mapper[stream].read_buffer
        try:
            for i in range(10):
                data = sock.recv(BUF_SIZE)
                if data:
                    readed += data
                else:
                    # connection closed by remote
                    self._mapper[stream].read_buffer = readed
                    return True
        except (IOError, OSError) as e:
            err = eventloop.errno_from_exception(e)
            if err not in (errno.EWOULDBLOCK, errno.EAGAIN):
                raise
        self._mapper[stream].read_buffer = readed
        return False

    def handle_once(self, stream, fd, event):
        # read event may be unregistered by other one, when the event is
        # in the fired event list, if so, we not handle it anymore.
        if event & (~eventloop.POLL_OUT) & self._mapper[stream].stream:
            logging.debug('{}[{}] POLL_IN event'.format(stream, fd))
            try:
                closed = self._handle_read(stream)
            except Exception as e:     # catch all errors, when handling event
                shell.print_exception(e)
                self._stage = STAGE_WAIT_DESTROY
                return
            self.process(stream)
            if closed:  # connectting closed by remote
                if self._stage == STAGE_STREAM:
                    # send the out band data in
                    # write_buffer of the other side
                    remote = 'remote' if stream == 'local' else 'local'
                    if self._mapper[remote].write_buffer:
                        self._stage = STAGE_WAIT_CLOSE
                        self._update_stream(remote, WAIT_STATUS_WRITING)
                    else:
                        # if write_buffer of the other side is empty,
                        # just change stage to STAGE_WAIT_DESTROY
                        self._stage = STAGE_WAIT_DESTROY
                else:
                    self._stage = STAGE_WAIT_DESTROY
                self._destroy(stream)
                return  # connecting closed, do not handle wirte event
            else:
                if self._stage == STAGE_STREAM:
                    # do not wait read event,
                    # until write_buffer of the other side is empty
                    self._unregister_event(stream, WAIT_STATUS_READING)

        if event & (~eventloop.POLL_IN) & self._mapper[stream].stream:
            logging.debug('{}[{}] POLL_OUT event'.format(stream, fd))
            try:
                complete = self._handle_write(stream)
            except Exception as e:
                shell.print_exception(e)
                self._stage = STAGE_WAIT_DESTROY
                return
            if complete:
                if self._stage == STAGE_STREAM:
                    self._unregister_event(stream, WAIT_STATUS_WRITING)
                    remote = 'remote' if stream == 'local' else 'local'
                    self._register_event(remote, WAIT_STATUS_READING)
                elif self._stage == STAGE_WAIT_CLOSE:
                    # out-of-band data send complete, wait destroy
                    self._stage = STAGE_WAIT_DESTROY
                    self._destroy(stream)
                else:
                    self._unregister_event(stream, WAIT_STATUS_WRITING)

    def process(self, stream):
        data = self._mapper[stream].read_buffer
        self._mapper[stream].read_buffer = b''
        if data:
            handler = self._handler_map[stream]
            handler(data)

    def handle_event(self, sock, fd, event):
        if self._stage == STAGE_WAIT_DESTROY:   # may not necessary
            self.destroy()
            return

        if sock == self._mapper['local'].sock:
            self.handle_once('local', fd, event)
        elif sock == self._mapper['remote'].sock:
            self.handle_once('remote', fd, event)

        if self._stage < STAGE_WAIT_DESTROY:
            self._update_activity(self)
        else:
            self.destroy()

    def _update_stream(self, stream, status):
        if self._mapper[stream].stream != status:
            self._mapper[stream].stream = status
            self._eventloop.modify(self._mapper[stream].sock, status)

    def _register_event(self, stream, event):
        status = self._mapper[stream].stream | event
        self._update_stream(stream, status)

    def _unregister_event(self, stream, event):
        status = self._mapper[stream].stream & (~event)
        self._update_stream(stream, status)

    def _destroy(self, stream):
        self._mapper[stream].closed = True
        sock = self._mapper[stream].sock
        if sock:
            logging.debug('destroy {}, fd[{}]'
                          .format(stream, self._mapper[stream].fd))
            self._eventloop.remove(sock)
            sock.close()
            self._mapper[stream].sock = None
            self._mapper[stream].read_buffer = b''
            self._mapper[stream].write_buffer.clear()

    def destroy(self):
        if not self.is_destroyed():
            self._destroyed = True
            self._dns_resolver.remove_callback(self._remote_connect)
            self._server.remove_handler(self)
            self._destroy('remote')
            self._destroy('local')


class LocalHandler:

    def local_write(self, data):
        if self._stage < STAGE_WAIT_DESTROY:
            self._mapper['local'].write_buffer.append(data)
            self._register_event('local', WAIT_STATUS_WRITING)

    def handle_data(self, data):
        if self._stage in (STAGE_STREAM, STAGE_CONNECTING,
                           STAGE_WAIT_CLOSE):
            self.handle_stream(data)
        elif self._stage == STAGE_INIT:
            self.handle_init(data)
        elif self._stage == STAGE_ADDR:
            self.handle_addr(data)
        else:
            logging.error('local[{}] unknown stage {}'
                          .format(self._mapper['local'].fd, self._stage))
            self._stage = STAGE_WAIT_DESTROY

    def handle_init(self, data):
        ALLOW, BADHEADER, NOTACCEPT = 0, 1, 2

        def _check_auth_method(data):
            # VER, NMETHODS, and at least 1 METHODS
            socks_version = common.ord(data[0])
            nmethods = common.ord(data[1])
            if socks_version != 5:
                logging.warning(
                    'local[{}] unsupported SOCKS5 protocol version {}'
                    .format(self._mapper['local'].fd, socks_version))
                return BADHEADER
            if nmethods < 1 or len(data) != nmethods + 2:
                logging.warning(
                    'local[{}] SOCKS5 NMETHODS and number of METHODS mismatch'
                    .format(self._mapper['local'].fd))
                return BADHEADER
            methods = data[2:]
            if METHOD_NOAUTH not in methods:
                logging.warning(
                    'local[{}] none of SOCKS5 METHODS requested'
                    ' by client is supported'
                    .format(self._mapper['local'].fd))
                return NOTACCEPT
            return ALLOW

        if len(data) < 3:
            # data is not long enough, so rewrite it to read_buffer
            # and return immediately
            self._mapper['local'].read_buffer = data
            return
        result = _check_auth_method(data)
        if result == ALLOW:
            self.local_write(b'\x05\x00')
            self._stage = STAGE_ADDR
        elif result == NOTACCEPT:
            self.local_write(b'\x05\xFF')
            logging.debug('local[{}] SOCKS5 METHOD not supported'
                          .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_CLOSE
        else:
            logging.debug('local[{}] SOCKS5 BAD header'
                          .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_DESTROY

    def handle_addr(self, data):
        def on_udp_associate(data):
            logging.debug('UDP associate, but not supported.')
            sock = self._mapper['local'].sock
            if sock.family == socket.AF_INET6:
                header = b'\x05\x00\x00\x04'
            else:
                header = b'\x05\x00\x00\x01'
            addr, port = sock.getsockname()[:2]
            addr_to_send = socket.inet_pton(sock.family, addr)
            port_to_send = struct.pack('>H', port)
            self.local_write(header + addr_to_send + port_to_send)
            self._stage = STAGE_WAIT_CLOSE

        def on_connect(data):
            header_result = parse_header(data)
            if header_result is None:
                logging.error('local[{}] can\'t parse SOCKS header'
                              .format(self._mapper['local'].fd))
                self._stage = STAGE_WAIT_DESTROY
                return
            atype, remote_addr, remote_port, header_length = header_result
            remote_addr = common.to_str(remote_addr)
            logging.info('connecting %s:%d from %s:%d'
                         % (remote_addr, remote_port,
                            self._mapper['local'].addr,
                            self._mapper['local'].port))
            self._stage = STAGE_CONNECTING
            # remote_write must call before remote_prepare
            self.remote_write(data)
            self.remote_prepare()

        if len(data) < 6:
            self._mapper['local'].read_buffer = data
            return
        cmd = common.ord(data[1])
        if cmd == CMD_UDP_ASSOCIATE:
            on_udp_associate(data)
        elif cmd == CMD_CONNECT:
            data = data[3:]
            on_connect(data)
        else:
            logging.error('local[{}] unknown SOCKS5 command {}'
                          .format(self._mapper['local'].fd, cmd))
            self._stage = STAGE_WAIT_DESTROY

    def handle_stream(self, data):
        self.remote_write(data)


class RemoteHandler:

    def remote_prepare(self):
        addr, port = self._chose_a_server()
        self._mapper['remote'].port = port
        self._dns_resolver.resolve(addr, self._remote_connect)

    def _chose_a_server(self):
        server = self._config['server']
        server_port = self._config['server_port']
        if type(server_port) == list:
            server_port = random.choice(server_port)
        if type(server) == list:
            server = random.choice(server)
        logging.debug('local[{}] chosen server: {}:{}'
                      .format(self._mapper['local'].fd, server, server_port))
        return server, server_port

    def _remote_connect(self, result, error):
        if self._stage != STAGE_CONNECTING:
            logging.debug('resolved dns but statg is no STAGE_CONNECTING')
            return

        if error or len(result) < 2:
            logging.debug('local[{}] get remote address error, {}'
                          .format(self._mapper['local'].fd, error))
            self._stage = STAGE_WAIT_DESTROY
            # maybe there is no event hanppend, when we wait to
            # connect to remote server, so we destroy it immediately
            self.destroy()
            return

        try:
            pipe_sock = self._create_remote_socket(
                    result[1], self._mapper['remote'].port)
        except Exception as e:
            shell.print_exception(e)
            logging.debug('local[{}] create remote socket error'
                          .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_DESTROY
            self.destroy()
            return
        if self.connectting(pipe_sock, result[1],
                            self._mapper['remote'].port):
            self._stage = STAGE_STREAM
            self.local_write(b'\x05\x00\x00\x01\x00\x00\x00\x00\x10\x10')
            self._mapper['remote'].sock = pipe_sock
            self._eventloop.add(pipe_sock,
                                eventloop.POLL_IN | eventloop.POLL_OUT,
                                self)
            logging.debug('local[{}] create remote socket[{}]'
                          .format(self._mapper['local'].fd,
                                  self._mapper['remote'].fd))
        else:
            pipe_sock.close()
            self._stage = STAGE_WAIT_DESTROY
            self.destroy()
            logging.error('fd[{}] cannot connect to {}:{}'
                          .format(self._mapper['local'].fd,
                                  result[1], self._mapper['remote'].port))

    def connectting(self, sock, ip, port):
        # trying to connect the remote pipe
        try:
            if self._fastopen:
                data = self._mapper['remote'].write_buffer[0]
                l = sock.sendto(data, MSG_FASTOPEN, (ip, port))
                if len(data) != l:
                    self._mapper['remote'].wirte_buffer[0] = data[l:]
                else:
                    del self._mapper['remote'].write_buffer[0]
            else:
                sock.connect((ip, port))
        except (OSError, IOError) as e:
            error = eventloop.errno_from_exception(e)
            if error == errno.ENOTCONN:
                if self._fastopen:
                    self._fastopen = False
                    logging.warn('fast open not supported')
                return False
            elif error == errno.EINPROGRESS:
                return True
            else:
                return False
        return True

    def process_data(self, data):
        data = self._encryptor.decrypt(data)
        if data:
            self.local_write(data)
        else:
            logging.error('remote[{}] decrpty data error'
                          .format(self._mapper['remote'].fd))
            self._stage = STAGE_WAIT_DESTROY

    def remote_write(self, data):
        # NOTICE: _pipe_sock may not be created,
        # because connection is nonblocking
        data = self._encryptor.encrypt(data)
        if not data:
            if self._stage >= STAGE_STREAM:
                logging.debug('remote[{}] encrypt data failed'
                              .format(self._mapper['remote'].fd))
            else:
                logging.debug('remote encrypt data failed')
            self._stage = STAGE_WAIT_DESTROY
            return
        self._mapper['remote'].write_buffer.append(data)
        if self._stage == STAGE_STREAM:
            self._register_event('remote', WAIT_STATUS_WRITING)


class LocalTCPRelayHandler(BaseHandler, LocalHandler, RemoteHandler):
    def __init__(self, server, local_sock,
                 loop, config, dns_resolver):
        BaseHandler.__init__(self)
        self._mapper = {
                'local': Mapper(sock=local_sock),
                'remote': Mapper(stream=WAIT_STATUS_READWRITING)
                }
        self._handler_map = {
            'local': self.handle_data,
            'remote': self.process_data
            }
        self._server = server
        self._config = config
        self._eventloop = loop
        self._dns_resolver = dns_resolver
        self._encryptor = encrypt.Encryptor(config['password'],
                                            config['method'])
        if 'forbidden_ip' in config:
            self._forbidden_iplist = config['forbidden_ip']
        else:
            self._forbidden_iplist = []
        self._fastopen = config['fast_open']
        self._update_activity = server._update_activity
        self._stage = STAGE_INIT


class ProxyHandler:

    def _remote_connect(self, result, error):
        if self._stage != STAGE_CONNECTING:
            logging.debug('resolved dns but stage is not STAGE_CONNECTING')
            return

        if error or len(result) < 2:
            logging.debug('local[{}] get remote address error, {}'
                          .format(self._mapper['local'].fd, error))
            self._stage = STAGE_WAIT_DESTROY
            self.destroy()
            return
        try:
            proxy_sock = self._create_remote_socket(
                    result[1], self._mapper['remote'].port)
        except Exception as e:
            logging.debug('local[{}] create remote socket error, {}'
                          .format(self._mapper['local'].fd, e))
            self._stage = STAGE_WAIT_DESTROY
            self.destroy()
            return
        # try to connect to remote
        try:
            proxy_sock.connect((result[1], self._mapper['remote'].port))
        except (OSError, IOError) as e:
            error = eventloop.errno_from_exception(e)
            if error != errno.EINPROGRESS:
                logging.debug('local[{}] can\'t connect to {}:{}'
                              .format(self._mapper['local'].fd,
                                      result[1], self._mapper['remote'].port))
                proxy_sock.close()
                self._stage = STAGE_WAIT_DESTROY
                self.destroy()
                return
        self._stage = STAGE_STREAM
        self._mapper['remote'].sock = proxy_sock
        self._eventloop.add(proxy_sock,
                            eventloop.POLL_IN | eventloop.POLL_OUT,
                            self)
        logging.debug('local[{}] create remote socket remote[{}]'
                      .format(self._mapper['local'].fd,
                              self._mapper['remote'].fd))

    def _remote_prepare(self, addr, port):
        self._mapper['remote'].port = port
        self._dns_resolver.resolve(addr, self._remote_connect)

    def _handle_addr(self, data):
        header_result = parse_header(data)
        if header_result is None:
            # raise Exception('can not parse header')
            logging.warn('local[{}] can\'t parse header'
                         .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_DESTROY
            return
        atype, remote_addr, remote_port, header_length = header_result
        remote_addr = common.to_str(remote_addr)
        logging.info('connecting %s:%d from %s:%d'
                     % (remote_addr, remote_port,
                         self._mapper['local'].addr,
                         self._mapper['local'].port))
        self._stage = STAGE_CONNECTING
        self._remote_prepare(remote_addr, remote_port)
        if len(data) > header_length:
            remain = data[header_length:]
            self.remote_write(remain)

    def _handle_stream(self, data):
        self.remote_write(data)

    def handle_data(self, raw_data):
        data = self._encryptor.decrypt(raw_data)
        if data:
            if self._stage in (STAGE_STREAM, STAGE_CONNECTING,
                               STAGE_WAIT_CLOSE):
                self._handle_stream(data)
            elif self._stage == STAGE_ADDR:
                if len(data) <= 3:
                    self._mapper['remote'].read_buffer = raw_data
                    return
                self._handle_addr(data)
            else:
                logging.debug('local[{}] unknown SOCKS5 stage'
                              .format(self._mapper['local'].fd))
                self._stage = STAGE_WAIT_DESTROY
        else:
            logging.debug('local[{}] decrypt data error'
                          .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_DESTROY

    def process_data(self, data):
        self.local_write(data)

    def local_write(self, data):
        data = self._encryptor.encrypt(data)
        if data:
            self._mapper['local'].write_buffer.append(data)
            self._register_event('local', WAIT_STATUS_WRITING)
        else:
            logging.debug('local[{}] encrypt data error'
                          .format(self._mapper['local'].fd))
            self._stage = STAGE_WAIT_DESTROY

    def remote_write(self, data):
        self._mapper['remote'].write_buffer.append(data)
        if self._stage == STAGE_STREAM:
            self._register_event('remote', WAIT_STATUS_WRITING)


class RemoteTCPRelayHandler(BaseHandler, ProxyHandler):
    def __init__(self, server, local_sock,
                 loop, config, dns_resolver):
        BaseHandler.__init__(self)
        self._mapper = {
            'local': Mapper(sock=local_sock),
            'remote': Mapper(stream=WAIT_STATUS_READWRITING)
        }
        self._handler_map = {
            'local': self.handle_data,
            'remote': self.process_data
        }
        self._server = server
        self._eventloop = loop
        self._config = config
        self._dns_resolver = dns_resolver
        self._encryptor = encrypt.Encryptor(config['password'],
                                            config['method'])
        if 'forbidden_ip' in config:
            self._forbidden_iplist = config['forbidden_ip']
        else:
            self._forbidden_iplist = []
        self._update_activity = server._update_activity
        self._stage = STAGE_ADDR
