#!/bin/bash
echo "# Raport Weryfikacji Asercji Yul"
echo "Data: $(date +"%Y-%m-%d %H:%M")"
echo ""
echo "## Podsumowanie"
echo ""

total_assertions=0
verifiable=0

for file in examples/*.yul; do
  result=$(./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen < "$file" 2>&1)
  
  name=$(basename "$file")
  found=$(echo "$result" | grep "Found" | grep -oE '[0-9]+')
  ver=$(echo "$result" | grep "Verifiable by Intuition" | grep -oE '[0-9]+ \(' | grep -oE '[0-9]+')
  
  echo "### $name"
  echo "- Asercje: $found"
  echo "- Weryfikowalne: $ver"
  echo ""
  
  total_assertions=$((total_assertions + found))
  verifiable=$((verifiable + ver))
done

percent=$((verifiable * 100 / total_assertions))

echo "## Łączne Statystyki"
echo ""
echo "- **Wszystkie asercje**: $total_assertions"
echo "- **Weryfikowalne przez Intuition**: $verifiable ($percent%)"
echo "- **Wymagają SMT**: $((total_assertions - verifiable)) ($((100 - percent))%)"
