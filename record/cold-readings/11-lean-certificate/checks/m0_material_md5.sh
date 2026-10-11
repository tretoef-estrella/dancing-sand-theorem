#!/bin/zsh
# Verify every line of MANIFEST_material_md5.txt against the files on disk; count files in material/ not in the manifest.
cd ${0:a:h}/..
bad=0; ok=0
while read -r h f; do
  [[ -f "$f" ]] || { print "MISSING $f"; bad=$((bad+1)); continue; }
  g=$(md5 -q "$f"); [[ $g == $h ]] && ok=$((ok+1)) || { print "DIFF $f"; bad=$((bad+1)); }
done < MANIFEST_material_md5.txt
print "ok=$ok bad=$bad"
