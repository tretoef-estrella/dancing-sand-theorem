# Grading of the first external cold reading of «The Dancing Sand Theorem»

Grepy Bross, auditor and only scribe of the hypercube project. Sunday 4 October 2026, 20:39–20:55 (times from `date`).

## 0. First line

**The cold reader's verdict «HOLDS» is accepted. Grade of the reading: HIGH MARK.** Every row of its chain is a derivation, not a stamp. Its independent code agrees with the theorem. Seven of its gates, re-run by me with its own scripts, reproduce its logs exactly. Its tables for n = 12 and n = 13 coincide with our own earlier measurement by another route.

**Consequence for the registers.** The Dancing Sand Theorem (the closed rule of flights 1–4 for the whole 2-part of K(Q_n), every n) moves from «proved by pencil, one reading» to:

> **PROVED (pencil, gated, read by a second reader)** — the top grade of this project's rule 8.

It holds **with the statement corrected** (§3 below). This is still not a human referee and not a publication.

## 1. What was graded

- **Reader:** «Grepy el lector frío del cubo 1», a fresh Claude in `~/Desktop/LECTORES_EN_FRIO/CUBO_DANCING_SAND_1/`.
  - It had no access to ARBOLYAML or to flight 8.
  - Rules declared and kept: no agents or workflows; every run inside `vigia.sh`; 18/18 logs end in `VIGIA-FIN-OK`; peak 533 MB.
- **Mission:** `MISSION.md`, md5 `ab96ce538f1671d50fec53acdadddea7`, unchanged.
- **Report:** `REPORT_COLD.md`, md5 `ba31b76816db9ff14e865b9b932280c6`, 294 lines, finished 20:06:52.
- **Copy of the whole delivery** (report, re-entry note, sealed file, diary, engines, logs, scratch): `reports/LECTOR_FRIO_1/delivered_2026-10-04/`, with `MANIFEST_md5.txt` (37 files). `material/` was not copied; it is our own copy and its 121 files matched the launch manifest, as the reader checked.

## 2. Is each HOLDS a derivation? Link by link

| link | what the reader did | my grade of its row |
|---|---|---|
| L1 fusion recursion | Re-derived the three isomorphisms; checked characters. Separated what is *used* (T_dance) from what is only a *name* (Donkin's tilting modules). Gate C-M0 64/64. | derivation ✔ |
| L2 RT′ | Re-did Lemma W with Kostant's formula; Ext¹ vanishing by filtrations; the mod-2 identity Δ(3) ⊕ V² written out; the lifting gf = 1 + 2h. Agreed that flight 3's citation-free proof replaces flight 1's Jantzen citation. | derivation ✔ |
| L3 moves, P-R1 | Did both eliminations (doblar and the even step) by hand. **Found that Theorem Z (Bier's basis) is not a link of the final chain**, only context. | derivation ✔; correct structural remark |
| L4 Theorem D | Re-did the coupled recursion, the windows and the coefficient recursion q ← q² − y_t q by hand. Gate G-L34 1230/1230, control fires 191. | derivation ✔ |
| L5 cost form | Deficit law; Legendre; the identity δ = G + γ. Rebuilt the cell constant αK + κ(m, K). Gate G-L5 87 360/87 360. | derivation ✔ |
| L6 Theorem O | Re-did Lemma B.3 and the multigraph induction. **Wrote the convexity step «d ≤ U at block ends ⟹ d ≤ Y», which the flights state in one word.** Gate G-L6 798/798. | derivation ✔; adds a missing paragraph |
| L7 Theorems U, F | Every step of 11.2.1–11.2.6, including the six (G) cases. Its own machine implementation of the construction, built from the definitions: λ ≤ 255, α ≤ 4, three prices, 0 failures. Brute-force floor 1898/1898. **Found the integer-splitting gap.** | derivation ✔; finds a real presentation gap |
| L8 tropical bound | Ultrametric inequality; integer version tied to the gap of L7. | derivation ✔ |
| L9 real cells, i = 0 | Penalty form; Legendre at i = 0 («m = −1»). Gates C4 686 169/686 169 and C4-i0 120/120. | derivation ✔ |

What it declared as **read but not redone by hand**:
- the E-side divided powers of Φ;
- Kostant's commutation formula (standard);
- flight 2 C.5's Kummer bookkeeping, replaced by three gates that check the equivalent statements.

These are honest limits, in the right place, and none sits on the critical path without a gate.

## 3. Its findings against us — all accepted

1. **The printed one-line statement was wrong by a constant.** This is MISSION §1, copied from AUDIT_FLIGHT_4 §4. My predecessor wrote it and I copied it without checking. The corrected statement, which I re-derived:
   - For every n ≥ 1, `Syl₂K(Q_n) ⊕ Z₂ ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}`, with `X(λ, i) = ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ ⊕_{D⊆I} Z/2^{e_D}`, where:
     - for i ≥ 1 (with m = i − 1, α = 1): `e_D = k + 2^k + κ(m, 2^k) + ŷ_D`;
     - ŷ is the integer antitonic fit of `x_D = R_m(D) − R_{m+2^k}(I∖D)` in o-order;
     - the integer splitting is part of the statement: a pool of p values with sum S becomes (S mod p) values ⌈S/p⌉, then ⌊S/p⌋;
     - for i = 0: e_∅ = ∞ (the free Z), and the other clocks are flight 1's naive clocks u(D), pooled the same way (the house m_low = 2^k − 1 with the row ∅ deleted).
   - **Check by hand:** λ = 6, i = 1: k = 2, I = {0, 1}, x = (1, 1, −1, −1), constant 2 + 4 + 0 = 6, so X(6, 1) = {1:4, 5:2, 7:2}. This agrees with our file THE_FIRST_OPEN_CELL_M6.
   - **Its gate C-R0:** 2520/2520 for the corrected form; the control without κ differs in 760 cells.
   - A note under AUDIT_FLIGHT_4 §4 records the correction (append-only).
2. **Integer splitting.**
   - AUDIT_FLIGHT_4 §2 accepted «no two adjacent blocks have equal non-integer means» as enough. It is not.
   - Counter-example x = (1, 2, 0, 1, 2, 2), checked by me by hand: the real blocks have means 3/2 and 5/4, and the integer split (2, 1 | 2, 1, 1, 1) is not antitonic.
   - What the proof needs: ⌊μ_A⌋ ≥ ⌈μ_B⌉ for adjacent blocks. It is true in every cell of the cube, by the same induction (its argument), and its gate P-INT covers 1 559 985 sequences.
   - **PRESENTATION, not a hole in the theorem.** It must be stated in the paper.
3. **Credit for m_λ(n).**
   - Doty–Henke does not give the multiplicities of T(λ) in V^{⊗n}.
   - The right credit is Donkin's characters and Larsen, arXiv:2405.16015 (2024) §2, with Tubbenhauer–Wedrich. Its check P-LARSEN gives 32/32, and the control fires 32/32; I re-ran it and got identical output.
   - ⚠️ **Larsen was quoted through the fetch tool, not read in the original.** The reader's sealed file says so («as quoted by the fetch tool»), but its §4.3 says «prints» without the caveat.
   - **Owed:** read Larsen in the original before crediting (house rule: an automatic reader's summary is not a reading). Note added under BARRIDO_NOVEDAD.
4. **Credit for the basis.** s_S = ∏(1 − x_i), in which the Laplacian becomes σ = U + 2D, is:
   - the Laplacian analogue of Chandler–Sin–Xiang §5 eq. (5);
   - Gao et al.'s change of variables u_i = x_i − 1 (proof of their Prop. 2.5).

   To be cited in the paper.
5. **New, it is honest about it:** what is new in L1/L2 is the integral statement RT′ (explicit lattices over Z₂), not the multiplicities.

## 4. My own re-runs (a sample of its gates, its own scripts)

- Copied into `reports/LECTOR_FRIO_1/rerun/`; the C engine was recompiled here.
- Logs in `logs/lector1_rerun_*.log`, all `VIGIA-FIN-OK`, peak 46 MB.

| gate | result | against its log |
|---|---|---|
| check1, n = 2..11, both forms of the rule against the direct Laplacian, both controls | PASS (10/10 «rule = direct: True; mission form = direct: True») | diff 0 |
| G-L5 | 87 360/87 360 | diff 0 |
| G-L6 | 798/798 | diff 0 |
| C4b (brute force, λ ≤ 30) | 1898/1898 three ways; 460 cells need pooling | diff 0 |
| P-INT | the example is non-antitonic | diff 0 |
| check23 (Bai, Gao, controls) | as reported | diff 0 |
| P-LARSEN | 32/32, control 32/32 | diff 0 |

**Independent route.** Its direct tables for n = 12 and n = 13 come from its own C Smith engine on the 2^n × 2^n Laplacian. They are identical, factor by factor, to our earlier measurement by the halving identity, which uses a different matrix and a different engine (`engines/cubo_mitad_3_12.log` line 10; `engines/cubo_mitad_13.log`, 89 s, 311 MB):

- n = 13: {1:2016, 2:364, 3:64, 4:364, 5:1, 7:560, 8:12, 9:364, 10:1, 11:336, 12:1, 14:12}.

A re-run with its own scripts checks reproducibility, not independence. The independence comes from its own engine, which it gated against PARI's matsnf (C-G0: 60/60 random matrices, 7/7 Laplacians), and from this cross with our halving route.

## 5. Weaknesses of the reading (said in the same size of type)

- Larsen's rule was quoted from a tool, not read in the original (above).
- Every sealed prediction held, at odds of 90–99 %. The reader says itself that this is a warning: they were predictions that the flights survive. Its controls are what show the checks could fail, and all of them fired.
- Scope cut in C4b (λ = 30 only up to i ≤ 12, against a sealed i ≤ 64). It was declared.
- Its counts against Bai are blind to the big clocks, and Gao's theorems are blind to where the column ruler is read. It said both when sealing. The ingredient «carries at m + K» is seen only by check 1 (n = 6, 10–13) and by check 4.
- Its web search: eleven queries on one search engine; Google Scholar and MathSciNet not searched; the JMU 2022 student project unreachable.
- Small slips, all self-reported (§7 of its report): an example written before it was computed, an estimate miscount, a self-referential md5 line.
- Side results of flights 1–4 not read (hall of mirrors, the fold-law pieces of flight 1, superseded parts of flights 3–4): declared.

## 6. What this grading does not cover

- The trophies of flights 5–6 (Gao Conj. 4.14, the poster's (n+1)-th factor, Gao Conj. 5.4 for every k). The reader checked them only by evaluating the rule up to n = 64; it did not read their proofs. **Their grade does not change:** proved by pencil, audited, one reading.
- The Dry and Wet Law (fold law) for every n: open; flight 8 is still flying.
- Priority: «first statement and proof of the whole 2-part», as far as its search and ours can tell. Not a guarantee.

## 7. What is owed before any paper

1. Print the corrected statement (§3.1), the integer-separation lemma (§3.2) and the convexity paragraph of L6.
2. Read Larsen arXiv:2405.16015 in the original. Downloading it needs Rafa's OK.
3. Fix the credits (Donkin, Larsen, Tubbenhauer–Wedrich; CSX eq. (5); Gao et al. Prop. 2.5).
4. Present Theorem Z as context, not as a link.
5. Rafa decides on the paper, the repository and Zenodo. Nothing is published.

## 8. My errors this turn

None in the mathematics. One of record: the statement I copied into MISSION §1 lacked the constant, and I did not check it against flight 1's D.5 before sending the mission. The reader caught it.

**Rule:** a theorem's one-line statement is checked against one worked cell before it is printed anywhere.

## Addendum (4 Oct 2026, ~20:55) — Larsen read in the original
Owed item §7.2 done: Larsen arXiv:2405.16015 v1 read in the original (`reports/LECTOR_FRIO_1/LARSEN_READ_IN_ORIGINAL_v1.md`). The reader's quotation is exact, including the T(0) exception; P-LARSEN stands on the original. The weakness of §5 (first bullet) is closed. Credits to print: Tubbenhauer–Wedrich 2021 (characters), Donkin 1993 (tilting ⊗ tilting), Larsen 2024 §2 (fusion of V^{⊗2}).
