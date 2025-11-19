#!/bin/bash
echo "=== Analiza typów asercji w przykładach Yul ==="
echo ""
for file in examples/*.yul; do
  echo "### $(basename $file)"
  grep -n "if.*invalid()" "$file" | head -10
  echo ""
done
