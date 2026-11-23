#!/bin/sh
set -eu

cd -- "$(dirname -- "$0")"
exec clojure -J-Xmx4g -M:start
