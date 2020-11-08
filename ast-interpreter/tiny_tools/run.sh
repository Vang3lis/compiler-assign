#!/usr/bin/env bash
set -euxo pipefail

 ./ast-interpreter "`cat $1`"
