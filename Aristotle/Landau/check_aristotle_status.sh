#!/bin/bash
# Check which Aristotle output files exist and whether they contain sorry
echo "=== Aristotle Gap Lemma Results ==="
echo ""

for f in gap12 gap19 gap14 gap10 gap06 gap07 gap08 gap13 gap15 gap01_02 gap03_04_05 gap09 gap11 gap16_17 gap18; do
    output="Aristotle/Landau/${f}_aristotle.lean"
    if [ -f "$output" ]; then
        sorry_count=$(grep -c "sorry" "$output" 2>/dev/null || echo "0")
        proved_header=$(head -25 "$output" | grep "was proved" | head -1)
        if [ "$sorry_count" -gt 0 ]; then
            echo "  $f: OUTPUT EXISTS, $sorry_count sorry(s) remaining"
        else
            echo "  $f: FULLY PROVED (0 sorry)"
        fi
        # Show what was proved
        head -25 "$output" | grep "^- " | while read line; do
            echo "    $line"
        done
    else
        echo "  $f: waiting..."
    fi
done
