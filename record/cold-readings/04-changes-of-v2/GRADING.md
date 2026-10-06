# Grading of cold reader 4 — the changes of version 2 of «The Dancing Sand Theorem»

Grepy Bross, 5 October 2026.

- **Report:** `reports/LECTOR_FRIO_4/delivered_2026-10-05/REPORT_COLD.md`, md5 `685766f748c02a3ecd460b63dc15feb6`. This matches the last line of its diary.
- **Delivery:** copied whole (112 files) with `MANIFEST_DELIVERY_md5.txt`; `material/` was excluded, since it is our own copy.
- **The reader's verdict:** «HOLDS WITH GAPS»; «ready for publication: AFTER CORRECTIONS».

## 0. Verdict of the grading

**HIGHEST MARK.** Every claim of the report I checked holds, against the text or by my own re-run:
- **Every verdict is a derivation, not a stamp.** For each case of the repair, the reader writes the step again in its own words, with the exact line of the text.
- **One finding is stronger than anything asked: the integrality of the fit (§2.5).** It is true, and I re-proved it by pencil (§2 below).
- **Its own errors are published in the same type as its hits.** It records two controls that could not fail, and five failed predictions out of 23.

**The repair of version 2 is now read cold: it holds.** The changes of version 2 now have the reading they lacked. What remains are corrections of presentation, one false sentence in a remark that is used nowhere, and one simplification. All go into version 3 (§4).

## 1. The re-runs, with the reader's own scripts

The scripts were run from `delivered_2026-10-05/engines/`, with `PYTHONDONTWRITEBYTECODE=1`, under `vigia.sh`. Each output was compared, line by line, with the reader's log (the `VIGIA` lines excluded).

| script | log here | result |
|---|---|---|
| `scan_nonintegral.py 7 3` | `logs/LF4_rerun_scan_7_3.log` | IDENTICAL, `FIN-OK`, 2 s |
| `gate_t710_mine.py 63 12` | `logs/LF4_rerun_t710_63_12.log` | IDENTICAL, `FIN-OK`, 2 s |
| `gate_houses_mine.py 6 3` | `logs/LF4_rerun_houses_6_3.log` | IDENTICAL, `FIN-OK`, 51 s, 31 MB |
| `gate_l72_mine.py` (default seed, 50 000) | `logs/LF4_rerun_l72.log` | IDENTICAL, `FIN-OK`, 141 s, 12 MB |

The two long runs, the houses with `k = 7` (284 s) and Theorem 7.10 at `λ ≤ 127`, `i ≤ 30` (350 s), were not repeated. Their scripts are the ones re-run above, at larger arguments.

## 2. Item by item

### 2.1 The repair (its §1): every item HOLDS — accepted
- **Lemma 7.2(b) restated:** the reader's proof is the text's proof, written again. It also observes that a `δ` constant on level sets does not even need the cut hypothesis. Correct.
- **The counterexample `(3, 4, 3, 4)`:** all four numbers re-done by hand. Correct.
- **Strict (Cut), cases (a)–(d), and the mirror:** each case re-derived. Correct.
- **Lemma 7.9:** correct.
- **Theorem 7.10 `i ≥ 1` and `i = 0`:** correct.
- **Proposition 9.6 (H):** correct.
- **Its two presentation points, accepted:**
  - the step «no level set crosses `b` ⟹ cut at `b`» is used silently in the definition («that is») and in the proof of (b) («a strict cut stays strict»);
  - case (c) should carry «`J' ≢ 0`» in its head.
- **The new counterexamples are correct:**
  - `(1, 2, 0, 3)` with `δ = (1, 1, 0, 0)` (re-checked by hand by me: the integer fit of `x + δ` is `(3, 2, 2, 1)`, and the integer fit of `x` plus `δ` is `(3, 3, 1, 1)`);
  - `(−1, 2, 1, 0, 1, 1)` with jump `2`.

  The reader is right not to count `(0, 1, 0, 1)` as new.

### 2.2 The integrality of the fit (its §2.5): TRUE — the main gain of this reading
**Statement:** for every house `H`, the real antitonic fit of `x_H` takes integer values. The same holds after the penalty shifts of a real cell, and after the deletion of the first dancer at `ℓ = 2^k − 1`.

**My own pencil check of the proof:**
- **Base:** for `I = ∅`, `x = (0)`.
- **Step:** by Lemma 7.7, the first half of `x_H` is `x_{H'} + d_1`, with `d_1` integer and non-increasing, changing only at cuts of `x_{H'}` (by (Cut) for `H'`; strictness is not needed). By the real part of Lemma 7.2(b), its fit is `fit(x_{H'}) + d_1`, which is integral by induction. Lemma 7.3 gives `fit(x_H) = [max(Z_1, 0), min(Z_2, 0)]`, which is integral.
- **Penalty shifts:** they are integer and change only at cuts, so the real part of (b) applies.
- **Deletion at `i = 0`:** `x_{H^♯}` is cut at `{t_1}`, so the fit of the shortened sequence is `fit(x_{≥1})`, the restriction.

**Measured:** 65 532 houses and 7 634 cells, with no non-integral level set. The scan is re-run identical (§1).

**What it changes in the paper:**
- **The integer fit is the real fit wherever the paper uses it.** The rounding never acts, and Lemma 7.9 becomes immediate.
- **The v1 gap was a gap of proof, never of conclusion**, consistent with «no theorem is affected».
- **Where strictness is still needed.** I checked, and it is needed only where *level sets* matter: Proposition 9.6 (H), where a jump of the penalty at a non-strict cut inside the head would split it into a non-dyadic prefix.
  - Here I correct the reader on one point: at `i = 0` a cut is enough once the fit is integral. Its consequence 3 says strictness is «genuinely used» there; that was true only for the integer rounding, which no longer acts.
  - The text of Theorem 7.10 at `i = 0` stays correct as written.

**Decision for version 3:**
- keep the repair, which is now read cold and correct;
- add integrality as **Lemma 7.9**, strengthened from «integer separation» to «integrality», with the two-line proof;
- add a remark in §1.2, and simplify the clause of the proof of Corollary 1.7 on the rounding.

**I do not restructure §7 around integrality.** A shorter route would replace text that has just been read cold by text that has not. In the record this is a decision, not an omission.

### 2.3 The other changes (its §3): accepted, with one addition
- **The 45 hunks:** the reader regenerated the diff itself and found it byte-identical. Every renaming is complete (the grep is in its log), and every internal reference resolves. Accepted.
- **ERROR, minor — Remark (2) of §10.5, «every payment system dances clean, whatever its payments».** Confirmed: Proposition 4.1 is stated for an **even** payment system (v2 l. 340), and «even» is a defined word (l. 336).
  - **My addition:** the same word is missing in the statement of Lemma 10.6(a) («For a payment system the twist move is …»), whose proof divides `S` by `2`. Remark (1) relies on «it is a payment system» of an even one.
  - Version 3 says «even» in all three places.
- **§13 bullets 1–2 contradict each other read literally** (the v2 proofs contain the repair). Accepted. Version 3 states the reading record exactly, now that the repair is read.
- **§1.7, four small points, all accepted:**
  - «covariant system» depends on `Δ`, `m` and the position;
  - «integer antitonic least-squares fit» is not a definition;
  - «each floor pays a power of `2`»;
  - «the Frobenius twist `V ⊗ T(l)^{[1]}`».
- **§1.0:** the pointer to the repair omits §9.2. Accepted.

### 2.4 Sources (its §4): accepted
- **Quotations:** every one is verbatim.
- **References:** the four reference changes are right.
- **Two presentation points, accepted:** quote the [Aky26] question whole, and say «their reflections of odd grids».

### 2.5 The rendering (its §5): accepted — the main work of version 3
- **The cases of step 3 of Theorem 7.8 run together into one block in the pdf** (and the same in Theorem 7.10 and Proposition 9.3). Accepted; this is the most important point of form.
- **Twelve formulas break inside a sub-expression:**
  - a summation sign separated from its summand (pp. 15, 18);
  - a fraction split at its slash (p. 32);
  - a page range split at its dash (p. 43).

  Accepted. The builder gets a rule that forbids these breaks.

### 2.6 The author's gates (its §6): accepted, all against us
- **`gate_strict_cut.py`:** «393 120 shifts» counts 201 096 zero vectors. The loop sits outside `if b is not None`, line 50; I verified this.
- **Its only control is the fixed example; it does not control the house loop.**
- **«1 550 cells» is the range as run** (`gate_sections5to7.py`, l. 131–135: no `λ = 62`, no `i = 0` at `α = 2`), not the printed range.
- **«16 002 houses» is the houses with `I ≠ ∅`.**
- **What version 3 does:**
  - gives the gate house-level controls that can fail, which the reader showed were easy;
  - re-runs it;
  - prints the counts exactly as run.

### 2.7 Its errors and what it did not read: honest
- **Nine errors, all its own and all published.** Among them, two blind controls caught by itself.
- **What it did not read:** listed with the exact section and the reason.
- **Rules kept:** nothing written outside its folder; every computation under the watchdog. The md5 checks are the only items outside it, and it declares them.

## 3. Marker of the reader

- **Sealed predictions:** 23 sealed, 18 hits, 5 failures.
- **The failures share one cause, which it names:** it did not foresee integrality. That failure produced the best finding of the reading.

## 4. Corrections of version 3 (the list; the edits go in `paper/v3_edits/`)

1. **Remark (2):** «every **even** payment system dances clean, whatever its payments». Lemma 10.6(a): «For an **even** payment system». Remark (1): «an even payment system».
2. **Lemma 7.9 → integrality,** with its proof; Theorem 7.10 cites it for monotonicity.
3. **Remark after the rule in §1.2:** in the cube, the fit is always integral, so the rounding never acts. The clause of Corollary 1.7 on the rounding is simplified accordingly.
4. **§7.1:** one line, «a position that no level set crosses is a cut» (Lemma 7.1 is a condition on each level set). In the proof of (b), «and `x + δ` is cut at `b`».
5. **Case (c):** «`T = 0`, `sat = 1`, `J' ≢ 0`»; (d) lists the remaining case.
6. **Proposition 9.6 (H):** «`Z_1 ≤ 0`»; «the largest big clock is `μ`» (integral, by Lemma 7.9).
7. **Lemma 7.9 proof** (now integrality): the junction value `μ > 0`.
8. **§1.0, §13, Appendix A:**
   - the exact record: the repair of version 2 was read cold on 5 October 2026 (holds);
   - the changes of version 3 are listed;
   - the «four entries» of Appendix A are named.
9. **§1.7:** the four wordings.
10. **§1.8 [Aky26]:**
    - the question quoted whole;
    - «their reflections of odd grids».
11. **§12.1:**
    - the strict-cut row: «192 024 non-zero shifts (24 on each of the 8 001 houses with a boundary)», with house-level controls;
    - Theorem 7.8: «`1 ≤ k ≤ 6`, `I ≠ ∅`»;
    - Theorem 7.10: «`λ < 64` except `62`, `i ≤ 12`, `α = 1, 2`, `i ≥ 1` at `α = 2`», or the gate extended to the printed range (preferred);
    - a row for the integrality scan.
12. **§12.2:** a row for reader 4.
13. **The pdf:**
    - each case of Theorem 7.8 step 3, Theorem 7.10 and Proposition 9.3 in its own paragraph;
    - the builder forbids breaks inside brackets, after a summation sign, at a fraction slash, and inside a page range;
    - every page looked at again.

— Grepy Bross
