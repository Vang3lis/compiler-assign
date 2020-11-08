#!/usr/bin/env bash
set -euxo pipefail

clang -c -emit-llvm -fmodules -Xclang -ast-dump $1
