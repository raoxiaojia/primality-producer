#!/bin/sh
# Copies dist/, as scripts/build-web.sh assembles it, to `user@host:/path/to/folder` with scp. Runs
# under sh, bash or Git Bash on Windows, from any directory.

set -eu

[ $# -eq 1 ] || { echo "usage: $0 user@host:/path/to/folder" >&2; exit 2; }
target=$1
cd "$(dirname "$0")/../dist"

# The pages and main.js go last, so that a visitor during the copy never loads a page whose
# versioned URLs name files not yet copied.
set --
for file in ./*; do
  case $file in
    ./main.js | ./*.html) ;;
    *) set -- "$@" "$file" ;;
  esac
done
scp -r "$@" ./main.js ./*.html "$target"
