#!/bin/zsh
# build_v2.sh — Grepy Escribano, 11 Oct 2026. Builds the Lean certificate v2 from version 1:
# make_v2.py (anchored edits) -> cold_fixes_REMATE.py (cold reading 13) -> paths_v2.py (published layout) -> fill_v2.py (Lean output from logs/CertCubo2.log,
# tables from data_v2/) -> cert_md2html.py -> paper/chrome_pdf.sh -> paper/pdf_meta.py (author and subject).
set -e
H=/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE; C=$H/lean/CERTIFICADO; N=$C/LEAN_CERTIFICATE_DANCING_SAND_v2
cd $C
python3 make_v2.py | tail -1
python3 cold_fixes_REMATE.py | tail -1
python3 paths_v2.py | tail -1
python3 fill_v2.py | tail -1
python3 cert_md2html.py $N.md $N.html 'The Dancing Sand Theorem — Lean certificate v2'
zsh $H/paper/chrome_pdf.sh $N.html $N.pdf
python3 $H/paper/pdf_meta.py $N.pdf 'Rafael Amichis Luengo' 'Lean certificate of The Dancing Sand Theorem, version 2'
md5 $N.src.md $N.md $N.pdf
