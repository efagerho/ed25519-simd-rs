#!/usr/bin/env bash
# Build the pinned static Intel XED kit outside the model source tree.
set -euo pipefail
dest=$(realpath -m "${1:?usage: build-kit.sh NEW_KIT_DIRECTORY}")
if [[ -e "$dest" ]]; then
    echo "Choose a new XED kit directory: $dest" >&2
    exit 1
fi
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
fetch() {
    git -C "$scratch" init -q "$1"
    git -C "$scratch/$1" fetch -q --depth 1 "https://github.com/intelxed/$1.git" "$2"
    git -C "$scratch/$1" checkout -q --detach FETCH_HEAD
}
fetch xed 0bcb6237345c5066726dcc08b3d87928df3b5b26
fetch mbuild 1b437e409221a2b5703b4d8896baa20d43e4ba1a
cd "$scratch/xed"
python3 mfile.py -j4 --install-dir="$dest" install
