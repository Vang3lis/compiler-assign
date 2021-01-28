#!/usr/bin/env bash
set -euxo pipefail


clang -emit-llvm -S $1 -o /tmp/a.ll
# cat /tmp/a.ll
clang -emit-llvm -g -c $1 -o /tmp/a.bc 
./assignment3 /tmp/a.bc
