#!/bin/bash
old_text=$1
new_text=$2
echo "Old text: ${old_text}"
echo "New text: ${new_text}"
grep -rlZ -- "${old_text}" . | xargs -0 gsed -i -e '1h;2,$H;$!d;g' -e "s/${old_text}/${new_text}/g"
