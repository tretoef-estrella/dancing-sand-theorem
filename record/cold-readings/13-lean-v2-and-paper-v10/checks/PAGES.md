# PAGES — Grepy Remate, cold reading 13

## Paper, v9 vs v10 (52 pages each; pdftoppm 40 dpi, PNG byte comparison; logs/render40.log)
Pages 2–47: byte-identical PNG at 40 dpi (46 pages). Pages 1 and 48–52 differ, as the author said.
p.01 — 90 dpi: only «version 10» in the byline differs; nothing broken.
p.48 — 90 dpi: §12.3 «What Lean proves» and «How»; new bullets and clause set well; `SmallCases.` / `G1_all` broken across a line like `Classical.` / `choice` in v9; nothing broken.
p.49 — 90 dpi: end of «Read cold» with the new sentence; «What Lean does not state» with three bullets; «Where … 69 pieces»; §13 reflowed; nothing broken.
p.50 — 90 dpi: reflow only (Acknowledgements, Appendix A); nothing broken.
p.51 — 90 dpi: «Formal verification» paragraph new; references start; nothing broken.
p.52 — 90 dpi: [LC26] with version 2, DOI and concept DOI; nothing broken.
pdftotext word comparison (page numbers removed; logs/words.log): the 25 word changes of the pdf are the 22 of the md plus three hyphenation reflows («forbidden», «statements», «modules») and one split of `SmallCases.G1_all` at a line end. No other text change.

## Certificate v2 (27 pages; pages carrying changed text located by pdftotext, logs/certpages.log; 90 dpi)
p.01 — title v2, byline line, companion line, §0 bullets, «Version 2» paragraph; nothing broken.
p.02 — §0 compilation sentence, «Read cold»; §1.1 start; nothing broken.
p.09 — §1.3 row DW with `SmallCases.DW'_one`, `SmallCases.DW'_all` (render as code); lower third of the page empty before the next table row (page break of a long table, as in v1); not broken.
p.10 — row Corollary 1.6, «Generality», §1.4 «Version 2», §1.5 start; nothing broken.
p.11 — §1.5 Lean block (fits the page, lines wrap as in §1.1); **BROKEN: in «The ten statements of the cases themselves are … `DW'_one` …» the name renders as italic mathematics «DW′ₒne» (prime, subscript o)** — C-9.
p.12 — §2 items 8–9 (`[[V2READ]]` placeholder, expected), §3 start; nothing broken.
p.15 — §3 table, row C53: **BROKEN: `DW'_one` renders «DW′ₒne» and **`DW'_all`** renders bold-italic «DW′ₐll»** — C-9; rest of row fine.
p.16 — §3.3 text and table rows of version 2; «the four `_all` statements» renders `_all` in italic (readable; style doubt).
p.17 — union row of version 2, «76 outside», §4 forbidden constructs, `decide` 17 files; nothing broken.
p.18 — §4 axioms (C53 sentence before «The last seventeen» — C-5, text order, not typesetting), register; §5 start; nothing broken.
p.20 — §6 bullets and paragraph «Version 2 adds the row of C53»; nothing broken.
p.22 — Table 6a row C53, Table 6b start; nothing broken.
p.23 — Table 6b continued (no changed text of its own; carries the table); nothing broken.
p.24 — Table 6b rows C53, Main, Total (thin spaces in «61285», «25559» not shown in bold cells; as in v1's total row style); §7 table and 3 470 bullet; nothing broken.
p.25 — §7 bullets (69 scripts, calendar C53, register 541), §8 commands (420, the three `2` check files); nothing broken.
p.26 — §8 «Version 2» paragraph (before «Then …», C-8: order), fingerprints, §9 «69 pieces»; nothing broken.
p.27 — reference to paper version 10; nothing broken.
