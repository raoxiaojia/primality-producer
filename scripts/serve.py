#!/usr/bin/env python3
"""Static file server for the page (dev only).

usage: serve.py [DIRECTORY] [PORT] [--host HOST]

Serves DIRECTORY (default the project's dist/, or web/ when there is no dist/) on PORT (default
8000) and HOST (default 127.0.0.1). An all-digits positional is the port.
"""

import http.server
import os
import sys
from functools import partial

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Handler(http.server.SimpleHTTPRequestHandler):
    """Sends `application/wasm` for `WebAssembly.instantiateStreaming`, `text/javascript` for `.js`
    (Windows may register it as text/plain) and `Cache-Control: no-store`, so a rebuilt page is
    never served stale."""

    extensions_map = {
        **http.server.SimpleHTTPRequestHandler.extensions_map,
        ".wasm": "application/wasm",
        ".js": "text/javascript",
        ".mjs": "text/javascript",
        ".html": "text/html; charset=utf-8",
        ".css": "text/css; charset=utf-8",
    }

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()


def parse_args(argv):
    """The (directory, port, host) named by the arguments."""
    directory = None
    port = 8000
    host = "127.0.0.1"
    positionals = []
    rest = iter(argv)
    for arg in rest:
        if arg == "--host":
            host = next(rest, None)
            if host is None:
                sys.exit("--host needs a value")
        elif arg in ("-h", "--help"):
            print(__doc__.strip())
            sys.exit(0)
        else:
            positionals.append(arg)
    for arg in positionals:
        if arg.isdigit():
            port = int(arg)
        elif directory is None:
            directory = arg
        else:
            sys.exit(f"unexpected argument {arg!r}")
    return default_directory() if directory is None else directory, port, host


def default_directory():
    """dist/ when it exists, else web/, both relative to the project root."""
    for name in ("dist", "web"):
        candidate = os.path.join(PROJECT_ROOT, name)
        if os.path.isdir(candidate):
            return candidate
    sys.exit("neither dist/ nor web/ exists; build the page or pass a directory")


def main():
    directory, port, host = parse_args(sys.argv[1:])
    if not os.path.isdir(directory):
        sys.exit(f"not a directory: {directory}")
    handler = partial(Handler, directory=directory)
    with http.server.ThreadingHTTPServer((host, port), handler) as server:
        print(f"Serving {os.path.abspath(directory)} at http://{host}:{port}/", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
