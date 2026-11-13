#!/bin/sh
# Builds the wasm package with wasm-pack and assembles dist/, the deployable static site. With
# `--deploy user@host:/path/to/folder` it then copies dist/ there with scp. Runs under sh, bash or
# Git Bash on Windows, from any directory.

set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
dist="$root/dist"
deploy=
case "${1:-}" in
  --deploy)
    [ $# -eq 2 ] || { echo "usage: $0 [--deploy user@host:/path/to/folder]" >&2; exit 2; }
    deploy=$2
    ;;
  '') ;;
  *) echo "usage: $0 [--deploy user@host:/path/to/folder]" >&2; exit 2 ;;
esac

cd "$root"
wasm-pack build --target web --release --no-typescript --out-dir web/pkg

rm -rf "$dist"
mkdir -p "$dist/pkg"
for name in index.html credits.html style.css main.js worker.js gallery.json; do
  cp "web/$name" "$dist/"
done
cp web/pkg/*.js web/pkg/*.wasm "$dist/pkg/"
cp LICENSE "$dist/"

# The page's URLs of its own files end in `?v=dev`. In dist/ they carry a checksum of the files
# instead, so that after a redeploy a browser fetches every file anew.
version=$(cat "$dist"/*.* "$dist"/pkg/* | cksum | cut -d ' ' -f 1)
for file in "$dist"/*.html "$dist"/*.js; do
  sed "s/?v=dev/?v=$version/g" "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
done

echo "dist/ assembled:"
(cd "$dist" && find . -type f | sort | while read -r file; do
  printf '%12s bytes  %s\n' "$(wc -c < "$file")" "${file#./}"
done)

if [ -n "$deploy" ]; then
  echo "copying dist/ to $deploy"
  scp -r "$dist"/* "$deploy/"
fi
