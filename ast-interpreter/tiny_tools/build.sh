#!/usr/bin/env bash
set -euxo pipefail

cmake -DLLVM_DIR=/usr/local/llvm10ra/
make
