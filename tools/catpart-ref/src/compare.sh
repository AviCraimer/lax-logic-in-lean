#!/bin/bash
cd "$(dirname "$0")"
for f in bad comment comment2 fileinfo find find_route find_route_altered find_routes harrison mid_test test test2 test3 test5 test6; do
  echo "=== $f ==="
  if [ ! -f "$f.frm" ]; then
    echo "no preserved $f.frm to compare against"
    if [ -f "$f.out.frm" ]; then
      echo "  ($f.out.frm generated, $(wc -c < "$f.out.frm" | tr -d ' ') bytes)"
    fi
  elif [ -f "$f.out.frm" ]; then
    ls -la "$f.frm" "$f.out.frm" | awk '{print $5, $NF}'
    if cmp -s "$f.frm" "$f.out.frm"; then
      echo "BYTE-IDENTICAL"
    else
      echo "DIFFERS -- diff line count:"
      diff "$f.frm" "$f.out.frm" 2>&1 | wc -l
    fi
  else
    echo "no .out.frm produced (process failed before write)"
    ls -la "$f.frm"
  fi
done
