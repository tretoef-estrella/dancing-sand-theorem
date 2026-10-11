#!/bin/zsh
# M3: git HEAD of each package in material/project/.lake/packages against the revs of lake-manifest.json.
cd ${0:a:h}/../material/project
for p in .lake/packages/*; do
  h=$(cat $p/.git/HEAD); n=${p:t}
  if grep -q "\"rev\": \"$h\"" lake-manifest.json; then print "$n $h in manifest: yes"; else print "$n $h in manifest: NO"; fi
done
print "mathlib lean-toolchain: $(cat .lake/packages/mathlib/lean-toolchain)"
