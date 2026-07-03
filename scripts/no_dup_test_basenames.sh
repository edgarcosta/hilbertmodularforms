#!/bin/sh
# Fail if any .m basename appears in more than one test directory.
# The Makefile's check/%.m and debug/%.m pattern rules collapse on a shared
# basename, so a duplicate would silently run the wrong file.
set -eu
dups=$(ls -1 Tests/*.m examples/*.m examples/slow/*.m 2>/dev/null \
       | xargs -n1 basename | sort | uniq -d)
if [ -n "$dups" ]; then
  echo "Duplicate test basenames across Tests/ and examples/:"
  echo "$dups"
  exit 1
fi
