# Sealed predictions — Grepy Remate (written before measuring)

P1. The tarball's RequestProject/ equals material/project/RequestProject/ file by file (420 .lean files in the clone).
P2. The 416 files of MANIFEST_md5_416.txt are unchanged; SmallCases/ is the only new folder.
P3. The 14 Lean statements match the piece; only renaming L1-1 -> L1_one (plus S0.. names as given).
P4. No forbidden construct in the four files (sorry, admit, axiom, native_decide, opaque, unsafe, implemented_by, extern, set_option, partial).
P5. CheckC53.lean runs exit 0, ~3 min, under the 4.5 GB Lean cap; axioms only propext, Classical.choice, Quot.sound.
P6. The paper diff touches only the header, §12.3 and Appendix A / [LC26]; no number of a result changes.
P7. At least one small slip somewhere in the new text of paper v10 or certificate v2 (a count, a name, or a "416/420" figure) — my weak prior: 50%.
P8. My own count of .lean files / lines / declarations reproduces 420 / 61 285 / 3 470 if the counting convention is the author's; the exact line figure depends on convention (wc -l vs non-empty).
P9. Paper pdf v9 vs v10: pages differ exactly at 1 and 48-52.
P10. Acceptance list: 12/12 pass on v10, 12/12 fail in control.
P11. msgC53.txt = instruction + separator + C53_the_small_cases.md byte for byte.
