# Sealed predictions — Grepy Cotejo (written after reading the diff text only, before any measurement)

Sealed at: 2026-10-11 10:27:01

P1. My own `diff -u v8.md v9.md` equals DIFF_v8_to_v9.txt apart from the two header lines; it has 9 hunks (I count 9 @@ in the given file, not the 14 the mission announces).
P2. `lean/project/RequestProject/` + Main.lean: 416 `.lean` files; the «415 Lean files» of §12.3 is the count without Main.lean (or without something else) — I predict the sentence is at least ambiguous with «416 modules».
P3. 60 940 lines: reproduces with `wc -l` over the 415 files without Main.lean (50 % confidence).
P4. 3 449 theorem+lemma declarations: reproduces (70 %).
P5. Table 6a: at most 2 rows of 68 disagree with the brute-force logs (60 %).
P6. §4 of the certificate: 885 `#print axioms` lines = 868 + 12 + 4 + 1 reproduce (70 %).
P7. Acceptance list: 12/12 pass on v9, 12/12 fail in control mode (80 %).
P8. v8 md built with md2html_v9.py is byte-identical to the v8 html (80 %).
P9. Pages 6–42 of v9 are image-identical to pages of v8 at 40 dpi (75 %).
P10. I will find at least one false sentence in the new text of v9 (60 %); the most likely place is §12.3 (counts or «Read cold»).
P11. No numbered statement or result number changed v8→v9 (90 %).
