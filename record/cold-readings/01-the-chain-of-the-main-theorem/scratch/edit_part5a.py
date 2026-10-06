# -*- coding: utf-8 -*-
p = 'REPORT_COLD.md'
s = open(p, encoding='utf-8').read()
s = s.replace("- **Chandler–Sin–Xiang** (arXiv:1511.00272v2, published 2017),",
              "- **Chandler–Sin–Xiang** (arXiv:1511.00272v2, 2015; the flights cite it as 2017, journal version not checked by me),")
old0 = "## 0. First line — does the Dancing Sand Theorem hold as stated: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD\n"
assert old0 in s
s = s.replace(old0, old0 + """
**HOLDS.** Every link L1–L9 HOLDS on my cold reading (re-derived in my own words, §2), and every check I wrote with my own code agrees: the direct Laplacian Smith form for n = 2..13 (12/12, controls fire), Bai's table and counts, Gao et al.'s Thm 4.1–4.2, and a machine check of the heart (Theorem F's construction on every house λ ≤ 255, α ≤ 4, three prices: 0 failures; brute-force floor 1898/1898). **Three PRESENTATION remarks, none affecting the truth:** (1) the one-line statement in MISSION §1 omits the additive constant k + 2^k + κ(i−1, 2^k) of the big clocks and the convention at i = 0 (the flights' own D.5 has them right); (2) «integer antitonic fit» needs a property (adjacent PAVA blocks separated by an integer) that the proof uses and the text justifies only in part — it is true in every cell, by the same induction; (3) the multiplicities m_λ(n) are known (Larsen 2024 prints the same fusion rule; Donkin's characters give them), and two basis choices are standard (CSX, Gao et al.) — credit to add. As far as eleven web searches and the sources given can tell, this is the first statement and proof of the whole 2-part of K(Q_n); independent human verification and publication remain the real test.
""")
old8 = "## 8. What I did not read\n"
assert old8 in s
s = s.replace(old8, old8 + """- **Not verified (side results, not links of the theorem):** FLIGHT1 Leg F (the hall of mirrors: catalogue, Theorem L / kiss matrix, K2, K3, N_lock), the fold law (D.4, P-F1..F3), Theorem B's controls; FLIGHT2 C.5–C.7 beyond what L6 needs; FLIGHT3 C.2–C.5 (Cauchy–Binet, salsa, St1, St2, the per-family machine check famcheck) and A.3 (Theorem A2) — superseded by Theorem F, read but not re-derived; FLIGHT4 A.1–A.8, §10 (the plumber P-F…P-F4) and the gold legs — superseded by §11, read but not verified.
- **Read but not redone by hand:** the E-side divided powers of Φ (FLIGHT2 A.1(b)); Kostant's commutation formula (standard, cited); FLIGHT2 C.5's Kummer bookkeeping u(D) − k = ρ_D + κ_{I∖D} + ε(D) (replaced by my gates C-R0, G-L5, G-L6, which check the equivalent statements).
- **Not opened:** the flights' engines (`material/engines_of_the_flights/`, by choice: my verdicts do not rest on them); the flights' SEALED files; Jantzen (not needed by RT′); the JMU 2022 project (unreachable); flight 4's `sources_4b/` (not in this folder).
- **Sources read only in part:** Gao et al. (statements of §1, §4, §5; not the proofs); CSX (§1–3, §5 start, §5.2); Doty–Henke (intro, §1–2 statements, §5 examples p = 2); Ducey et al. (abstract, §0–2 opening); Reiner–Tseng (abstract, §12.2); Anzis–Prasad (introduction). Bai: read whole.
""")
olde1 = "the lesson: no number goes in the report before it is computed.\n"
assert olde1 in s
s = s.replace(olde1, olde1 + """- **E2 (diary, G-L34 estimate line).** I wrote «1271 dance-lattice Smith forms» in the estimate; the run had 30 families × 41 shifts = 1230 cells. A miscount in the estimate only; corrected in the next diary line.
- **E3 (scope).** C4b was sealed for λ ≤ 30, i = 0..64; for λ = 30 (16 dancers, exhaustive DP over 2^16 column sets) I ran i = 0..12 only, for time. Declared in §3.4 and §6.
- **E4 (§3.1, first draft).** A garbled sentence about the n = 12 no-pooling control was written and corrected minutes later.
- **E5 (method).** My first C4 code (sets and tuples) would have needed far more than ten minutes for λ ≤ 255; I rewrote it with bitmasks **before** running it. No run was killed; every log ends in VIGIA-FIN-OK.
- **E6 (shell).** One here-document with non-ASCII text failed to parse as Python (encoding); the edit was redone from a script file (`scratch/edit_part5a.py`). Nothing was lost.
""")
open(p, 'w', encoding='utf-8').write(s)
print('ok')
