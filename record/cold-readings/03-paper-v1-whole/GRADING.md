# Grading of cold reader 3 — the paper «The Dancing Sand Theorem» v1, read whole

Grepy Bross, auditor of the cube, 5 October 2026.

**Delivery.**
- Report: `delivered_2026-10-05/REPORT_COLD.md`, md5 `1ce8224d915aece91ff1ca0e6836f0d8`, 961 lines, closed at 13:37:27 CEST.
- Copy of the reader's folder (without `material/`): 133 files, identical by md5 to the origin (`_MANIFEST_origin.txt` = `MANIFEST_md5_copy.txt`).

**First line of the report.** HOLDS WITH GAPS · AFTER CORRECTIONS.

## 0. Grade: HIGHEST MARK

Every verdict is a derivation, not a stamp. The reader re-derived the ~80 numbered statements of §2–§10 and the two assemblies in its own words.

It wrote its own engines for everything it checked. Every control it built fails where it must, and it caught one of its own controls that could not fail.

It found the first real defect in a printed proof of this project, with an explicit counterexample and a repair. It also found a quotation that changes its source's meaning, and four places where the verification record says more than was done. All of this was verified by the auditor below.

Its errors are declared (§8 of its report); none affects a result.

## 1. What I verified, and how

### 1.1 Lemma 7.2(b): the integer part is false as stated — CONFIRMED

**By hand.** `x = (3, 4, 3, 4)`. PAVA merges everything, so `fit(x) = (7/2)^4`. Since `fit(x_{<2})` and `fit(x_{≥2})` are both `(7/2, 7/2)`, `x` is cut at `2` in the sense of §7.1.

With `δ = (1, 1, 0, 0)`:
- `fit(x + δ) = (9/2, 9/2, 7/2, 7/2) = fit(x) + δ`, so the real part holds;
- the integer fit of `x + δ` is `(5, 4, 4, 3)`;
- the integer fit of `x`, plus `δ`, is `(4, 4, 3, 3) + δ = (5, 5, 3, 3)`.

The cause is in the sentence of the proof: «the level sets of `fit(x)` … are the level sets of `fit(x) + δ`». A level set may straddle a cut — a cut allows equal values on both sides — and a jump of `δ` splits it.

**Own gate.** `grading/gate_strict_cut.py`, written from §7.1 and §7.3; log `logs/grade3_strict_cut_6_4.log`, `VIGIA-FIN-OK`, 19 s, 10 MB. Over every house with `k ≤ 6` and `α ∈ {1, 2, 3}` (16 380 houses):
- the **strict** cut — `fit(x_H)` drops strictly at the boundary `b` of `J_H` and at its mirror — holds at all 8 001 boundaries;
- the integer shift of Lemma 7.2(b) holds for all 393 120 penalty shifts with `P_r, P_c ≤ 4`, as used in Theorem 7.10 (U2);
- the deletion of `∅` holds in all 360 houses with `ℓ = 2^k − 1`, as used in Theorem 7.10 at `i = 0`;
- **0 failures.**
- Control: the reader's counterexample breaks the integer shift, and it is a non-strict cut. Both fire.

**The reader's repair, re-derived.** Strengthen (Cut) in Theorem 7.8 to strict (Cut): if `J_H ≢ 0` and its boundary `b > 0`, then `fit(x_H)_{b−1} > fit(x_H)_b`, and the same at the mirror. It is proved inside the same induction:
- **case (a):** `d_1 = α2^c − hJ'` drops by `h ≥ 1` at `b`, and `Z_1 = fit(x_{H'}) + d_1` is positive at `b − 1`. So `max(Z_1, 0)` drops strictly.
- **case (b):** at the middle, the fit is `Z_1(I') > 0` before and `≤ 0` after.
- **case (c):** `d_2` drops by `κ = h ≥ 1` at `b' ∪ {c}`, and `Z_2 < 0` from there. If `b' = ∅`, the left neighbour is `I'`, where the fit is `≥ 0`.
- **the mirror:** by antisymmetry.

If `δ` is constant on every level set of `fit(x)`, the level sets of `fit(x) + δ` are those of `fit(x)`, shifted by integers. So the integer part of Lemma 7.2(b) holds whenever `δ` jumps only at strict cuts. That covers every use:
- Theorem 7.8 step 1;
- Lemma 7.9;
- Theorem 7.10 (U2) and `i = 0`;
- Proposition 9.5 (H).

**Verdict.**
- It is a GAP of the proof as printed, not an error of any theorem: no statement of the paper changes.
- **Correction:**
  - restate Lemma 7.2(b): the integer claim holds when `δ` is constant on every level set of `fit(x)`, in particular when it jumps only at strict cuts;
  - add strict (Cut) to Theorem 7.8, with the three-case proof above;
  - cite it at each use.
- **This part must be read cold again** (§4).

### 1.2 Remark (2) of §10.5 and the §12.2 note: not reproduced by the reader — EXPLAINED

**What the paper says.** «With generic payments `4q_d` in place of `4(d + c)`, or with floor-dependent odd units on `F`, cleanliness fails at depth (first at `l = 63`, resp. `l = 31`)».

**What the measurement behind it was.** I traced it to flight 9's engine `g9_explore.py`, function `e2`, and re-ran it read-only with the driver `grading/remark2_setup.py`, seed 11, `l ≤ 63`, four shifts:

| set-up | generic payments `4q_d` | odd units on `F` only |
|---|---|---|
| flight 9's weights: random constants `h_m ∈ [−5, 5]` | 245/248 clean, first failure `l = 63` (as in its log) | 169/248 clean, first failure **`l = 32`** |
| the paper's weights: Bernoulli `η_m` (the reader's set-up) | **248/248 clean** | **248/248 clean** |

Logs: `logs/grade3_remark2_{generic,oddU}_{rand,eta}.log`, all `VIGIA-FIN-OK`. The `l = 31` of the remark belongs to flight 9's kind `oddunits`, which puts odd units on the payment AND on `F` (184/248, first failure `l = 31`).

**Verdict.**
- The reader is right that the remark, as printed, is false under the natural reading with the operators of the paper.
- The measurement exists, but only with random constant weights, and the `l = 31` is attributed to the wrong perturbation.
- It is used nowhere.
- **Correction:** restate it exactly, or keep only the first sentence («`𝒦` is sufficient, not necessary»). If the numbers stay:
  - name the weights;
  - give the two thresholds (`l = 63`; `l = 32` with units on `F`, `l = 31` with units on `F` and on the payment);
  - publish the engine.
- **A side fact worth one sentence, measured and not proved:** with the Bernoulli weights, the dance stays clean even under both perturbations, for `l ≤ 63`.

### 1.3 The [Aky26] quotation — CONFIRMED, misleading

The source, `sources/TwoAdicAllOnesSquare_arXiv2609.10625.txt` (lines 566–567), reads: «Our odd-grid reflections have fixed vertices, however, so the fold is not a regular double cover and their splitting theorem does not apply directly. Can an analogous integral description **with fixed vertices** explain …».

Our ellipsis drops «with fixed vertices», and then we claim the fold law «is such a description». The antipodal fold is fixed-point free, the case they set aside.

**Correction:** say what they say. For regular double covers, the exact sequence of Reiner and Tseng splits away from the covering degree, so the prime 2 is where extra structure is to be found [Aky26, §4]. The fold law gives that structure for the antipodal involution of the cube, a regular double cover. Their question concerns folds with fixed vertices.

### 1.4 The verification record — CONFIRMED, four overstatements

- **Theorem 6.2 row.** It reads «all `I` with `|I| ≤ 4`». `paper/gate/gate_sections5to7.py` line 172 is `for s in range(0, 4)`, that is `|I| ≤ 3`; its comment says «≤ 4». My error, in the gate and in the paper. The reader's own gate reaches `s ≤ 5` with controls, so either the row cites that or it says `≤ 3`.
- **Theorem 7.8 row.** «48 006 houses» are house-checks (16 002 houses × 3 prices).
- **`gate_dance.py`.** It announces a control in a comment and implements none.
- **13 of 26 rows** have no control, and several rows rest on code not printed: Theorem 10.15 «covariance and `𝒦`», Lemma 10.8, Lemma 10.20, Theorem 10.22.

**Correction:**
- fix the three numbers;
- mark which rows have controls;
- publish every engine cited;
- move the process narrative (flights, readers) to a short appendix or supplement.

### 1.5 Honesty of the grades in §1.0 and §13 — CONFIRMED

§12.3 itself says that the printed proof of Theorem O (by top bits) and the organization of §10 are new in this text, so «read cold» did not apply to them. This reading is now their first cold reading, with verdict HOLDS. **After the corrections, the exact sentence is:**
- the whole text was read cold once, on 5 October 2026, by a reader with no access to the flights, the audits or the earlier readings;
- verdict «holds with gaps»;
- one gap in §7, repaired;
- the repaired §7 was read cold again.

That last line can only be written once it is true.

### 1.6 Re-runs of the reader's own checks (with its scripts, in `grading/rerun/`)

| script | result |
|---|---|
| `lemma72b_counterexample.py` | output identical to its log |
| `theoremF_check.py 7 6` | output identical to its log (26 s, 178 MB) |
| `theoremO_brute.py 5` | output identical to its log |
| `check31.py 1 9` | identical except one printed timing (0.1 s against 0.0 s); results JSON byte-identical |

The first run of `check31.py` exited 1 because my copy lacked `scratch/`. That was my set-up, not the reader's code.

### 1.7 Items accepted without separate re-check (PRESENTATION or minor, each traced to its line)

- the remark «`M` has at most `(λ + 1)/2` rows», false at `λ = 2` (2 rows); correct bound `⌊λ/2⌋ + 1`;
- the sign at `Δ = {0}` in the proof of Lemma 4.5;
- the sign of a zero difference in the proof of Proposition 5.3;
- the undefined `J` in the proof of Proposition 5.4;
- `Syl_2(Z ⊕ K)` at line 183;
- the count «`2(n − 2) ≥ n`» in Corollary 1.6, step 3;
- the missing line in Lemma 6.4;
- Weyl's complete reducibility over `Q`, used and not named (Proposition 3.1(d), Lemma 3.3), which makes Remark (2) after Theorem 3.6 slightly too strong;
- «an extension of two lattices is a lattice» (one sentence);
- the slot order of the moves is not the o-order (a re-indexing to state);
- Lemma K inside Proposition 9.5 (give it a number);
- the IKKY quotation silently corrected (quote with [sic]);
- credit GMMY Remark 4.4 for Lemma 9.2(b) and GMMY Proposition 2.12 in §1.7; mention GMMY Table 1;
- Bai counts invariant factors of `K(Q_n)`, the paper cyclic factors of `Syl_2` (one sentence);
- the notation change of GMMY's `c_i` (one sentence);
- `τ`, `κ`, `σ`, `φ`, `ε`, `h`, `c`, `a` overloaded — rename at least `τ`, `κ`, `σ`, `φ`, `ε`;
- `max(x, ≤ G)`;
- updated bibliographic data (DHS17 LAA 546 (2018); IKKY22 Adv. Appl. Math.; Yue23 EJC 31(1) (2024) P1.38; GMMY24 volume and pages);
- in §1.5, item 4, name Lemma 6.4;
- the PAVA tie convention (merge equal means), one warning sentence.

**The pdf defects of §5.5 of the report** are all real and are fixed when the pdf is rebuilt:
- formulas broken inside table cells (p. 2);
- `X(λ, i)` broken (p. 3);
- the exponent of Corollary 1.7 split (p. 5);
- `f_max` (p. 12);
- `rank/2` in code font (p. 13);
- the example matrix as a nested list (p. 14);
- a lone ∎ (p. 17);
- `𝔞` rendered as `a` (p. 32);
- the wrapped exponent (p. 34);
- numbers broken in the §12.2 table (p. 35).

### 1.8 Where the reader's verdict needs a nuance

On Remark (2) the reader wrote «ERROR or over-statement». The measurement exists and reproduces; what is wrong is the statement, not the data. «Over-statement, with the second threshold misattributed» is the exact grade. This is not a fault of the reader: the paper did not give it the weights.

## 2. The reader's errors (its §8), checked

All four are declared, all are in its diary, and none touches a result:
- one run killed by the watchdog for its own bug;
- one control that could not fail, caught and replaced, with the faulty logs kept;
- one sympy blow-up, killed by the watchdog;
- one parse run outside the watchdog.

## 3. My errors in this grading

1. **A stray `rm -f /dev/null`** at the head of a command line, a violation of the house rule «never `rm`».
   - It had no effect: `/dev/null` is owned by root, and I checked that it is intact.
   - Two engine copies I had made by mistake were moved to `_BORRAR/grade3_unneeded_copies/`, not deleted.
2. **The «`|I| ≤ 4`» of the gate and of §12.2 was mine,** in the original gate (comment against code).

## 4. What follows

1. **The corrections**, in one pass over md and pdf, every page looked at:
   - §1.1–§1.7 above;
   - the vocabulary section and the names chosen (`notes/GLOSARIO_PROPUESTO_v1.md`);
   - the exact reading record in §1.0, §12.3 and §13.
2. **A cold reading of the changes** by a new reader, with §7 (strict Cut and the restated Lemma 7.2(b)) as the main target, before anything is published.
3. **Then Zenodo,** when Rafa says so.

— Grepy Bross
