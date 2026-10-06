# The Dancing Sand Theorem — corrections from version 1 to version 2

Grepy Bross, 5 October 2026.

Version 1: md `27e6a7be…`, pdf `eb0871e7…` (moved to `paper/historico/`). Version 2: `paper/THE_DANCING_SAND_THEOREM_v2.md` and `.pdf`; their md5 are in the last section of this file.

Sources of the corrections:
- **[G]** the grading of cold reader 3, `reports/LECTOR_FRIO_3/CALIFICACION_LECTOR_FRIO_3_v1.md`, §1.1–§1.7;
- **[R]** the reader's report, `reports/LECTOR_FRIO_3/delivered_2026-10-05/REPORT_COLD.md`;
- **[N]** the names, chosen by right (Rafa's order), `notes/GLOSARIO_PROPUESTO_v1.md`;
- **[A]** found by the auditor in the read-through of the whole version 2.

Every edit was made by a script in `paper/v2_edits/` (`part1.py` … `part11.py`). Each replacement asserts the exact number of occurrences of its old text, so no edit was applied blind. The order of the parts is the order of the paper.

**No statement of a theorem changed.**

## 1. The gap: Lemma 7.2(b) and its uses [G §1.1, R]

- **§7.1, new definition.** A cut at `b` is **strict** if `fit(x)_{b−1} > fit(x)_b`.
- **Lemma 7.2(b), restated.** The real part is unchanged. The integer part now holds when `δ` is integer and constant on every level set of `fit(x)`, in particular when `δ` changes only at strict cuts. The proof is written out. A counterexample shows that the hypothesis is needed: `x = (3, 4, 3, 4)`, cut at `2` but not strictly, with `δ = (1, 1, 0, 0)`.
- **Theorem 7.8 (Cut), now strict.** The proof covers the cases (a), (b) and (c), with the mirror by antisymmetry. The case `b ≠ ∅` holds because `J_H(∅) = 0`.
- **Each use of Lemma 7.2(b) now cites the strict cut:**
  - step 1 of Theorem 7.8;
  - Lemma 7.9: «a non-increasing integer shift that is constant on every level set preserves the property» [A];
  - Theorem 7.10 (U2), and the deletion of the first dancer at `i = 0`;
  - Proposition 9.6 (H).
- **Gates:**
  - `gate/gate_strict_cut.py`, the grading's gate: 16 380 houses, 8 001 boundaries, 393 120 shifts, 360 deletions, 0 failures; the control fires.
  - `gate/gate_lemma72.py`, new: 20 000 random sequences, 0 failures; the control fires in 189 of 2 841 trials.
- **Status.** §1.0, §13 and Appendix A say that this repair has **not yet** been read cold.

## 2. Remark (2) of §10.5 [G §1.2, R]

The remark is restated with the exact measurement: the dances on `T(l)`, `l = 2, …, 63`, seed 11, 248 dances per case.
- Random payments `4q(d)`: 3 dances are not clean, all at `l = 63`.
- Odd floor-dependent `u(d)`: 79 are not clean, the first at `l = 32`.
- With the weights `η_m`: all 496 are clean.

It is labelled «used nowhere». Its code is published: `gate/remark2/`, with three engines of flight 9 copied unchanged (md5-identical) and a driver, `gate_remark2.py`. Logs: `logs/v2_remark2_*.log`.

## 3. The quotation of [Aky26] [G §1.3, R]

§1.8 quotes Akyar et al. whole, with their own frame: the prime `2` is «a natural place to look for additional structure under an involution». It also says what they ask (an integral description with fixed vertices) and why the cube differs: the antipodal fold has no fixed vertex.

## 4. The verification record, §12 [G §1.4, R]

- **§12 rewritten:** «12. Computations». §12.1 lists the checks published with the paper, with a **control** column, where «none» means none. §12.2 lists the re-computations by readers 1, 2 and 3. The process narrative moved to **Appendix A** (new).
- **Theorem 6.2:** the row now cites `gate/gate_theoremO.py` (new): `|I| ≤ 5`, 69 cases, controls firing in 42 and in 26 cases. The comment of `gate_sections5to7.py` now says `|I| ≤ 3` (61 cases), which is what its code does.
- **Theorem 7.8:** 16 002 houses, 48 006 house-checks (three prices).
- **`gate_dance.py`:** a real control. The closed form without `2^{o(Δ)}` differs from the dance in 420/420 cells and predicts a wrong Smith form in 262.
- **`gate_direct.py`:** rule controls. Without pooling it fails at `n = 6, 10`; without `h(D)` at `n = 2` and `4, …, 11`.
- **Rows that rested on code not printed** (Theorem 10.15, Lemma 10.8, Lemma 10.20, Theorem 10.22) left §12.1. They now appear in §12.2 under the reader who checked them, or not at all.
- **Logs of version 2:**
  - `logs/v2_gate_direct_11.log`
  - `logs/v2_gate_dance_40_6.log`
  - `logs/v2_gate_57_127_3.log`
  - `logs/v2_gate_s9_200.log`
  - `logs/v2_gate_s10_22_5.log`
  - `logs/v2_gate_theoremO_{4,5}.log`
  - `logs/v2_gate_lemma72.log`
  - `logs/v2_gate_strict_cut_6_4.log`
  - `logs/v2_remark2_*.log`

  Every log ends with `VIGIA-FIN-OK exit=0`, and every number in §12.1 matches its log. The gate files of version 1 are kept in `paper/gate_v1_record/`.

## 5. The reading record [G §1.5]

§1.0, §13 and Appendix A state the reading history exactly:
- the chains were read cold before the text was written;
- version 1 was read cold once, as a whole: «holds with gaps», one gap;
- version 2 repairs the gap;
- the changes of version 2 have not yet been read cold.

These sentences change when that reading exists.

## 6. Presentation and minor items [G §1.7, R]

- **§1.2, PAVA.** Adjacent blocks with equal means are merged.
- **§1.1, the IKKY quotation.** Quoted as written, with «[sic]».
- **§1.4, counting.** Bai counts the invariant factors of `K(Q_n)`; the paper counts the cyclic factors of `Syl_2`. One sentence relates the two. Another sentence relates Gao et al.'s `c_i` to ours.
- **§1.5, item 4.** It names Lemma 6.4.
- **§1.8, credits:**
  - GMMY Proposition 2.12 (the `F_2`-rank of the folded Laplacian);
  - GMMY Remark 4.4 (Lemma 9.2(b));
  - GMMY Table 1;
  - GMMY Proposition 1.9 (the odd part).
- **§2.1.** `(Z ⊕ K) ⊗ Z_2 ≅ Z_2 ⊕ Syl_2 K`, in place of «`Syl_2(Z ⊕ K)`».
- **Weyl's theorem on complete reducibility over `Q`** is named where it is used (Proposition 3.1(d), Lemma 3.3), and Remark (2) after Theorem 3.6 says so.
- **Lemma 3.3.** The extension of two lattices is decomposed into weight spaces by the interpolation polynomial and Newton's forward differences [A].
- **§4, the moves:**
  - «half the rank»;
  - the slot order is not the o-order, a re-indexing that is now stated;
  - the sign at `Δ = {0}` in the proof of Lemma 4.5;
  - the example matrix printed as a table;
  - the number of rows of `M` is at most `⌊λ/2⌋ + 1` (the old «`(λ + 1)/2`» failed at `λ = 2`).
- **§5–§6:**
  - the sign of a zero difference in the proof of Proposition 5.3;
  - the undefined `J` in the proof of Proposition 5.4;
  - the missing line in Lemma 6.4.
- **§9:**
  - Lemma K is now **Lemma 9.5**; Proposition 9.5 is **Proposition 9.6** («a ceiling for the big clocks»); Lemmas 9.6–9.8 become 9.7–9.9; Theorem 9.9 becomes 9.10;
  - in Corollary 1.6, step 3, the count «`2(n − 2) ≥ n`» is corrected, and `max(x, ≤ G)` is written out;
  - the proof names `A_0` and counts the `n + 1` factors.
- **References, checked against Crossref:**
  - [GMMY24]: *Comm. Algebra* 52 (2024), no. 10, 4459–4479;
  - [IKKY23]: *Adv. in Appl. Math.* 143 (2023) 102450;
  - [Yue24]: *Electron. J. Combin.* 31(1) (2024) P1.38;
  - [DHS18]: *Linear Algebra Appl.* 546 (2018) 154–168.

  The labels were changed in the text as well.
- **Theorem 10.22** [A]:
  - «`W_+ ≡ I` and `W_− ≡ −I (mod 2)`, so `W_+ − W_− ∈ 2·Mat(Z_2)`», in place of «`≡ 2I (mod 2)`»;
  - the case labels of Theorems 7.10 and 10.22 are printed as «The case `i ≥ 1`».
- **Theorem 10.15** [A]: the display of its four blocks is printed on two lines (it wrapped inside a fraction).
- **§1.7, golden matching** [A]: the vocabulary row says that it is the bijection `β_r`, and that its term is the unique term of least valuation.

## 7. Names [N, G §1.7]

**Renamed:**
- `τ(D)` (§5, §9) → `ψ(D)`, with `ψ_t = h_t − 2^t`;
- the saturation `σ_t` → `sat_t`;
- the matchings `σ`, `σ_r` → `β`, `β_r`;
- in Lemma 10.8, `κ_h`, `ρ_h` → `in_h`, `out_h`;
- the sign `ε` → explicit `(−1)^j`; `ε_L` → `e_L`;
- the functions of `𝒦`, `φ` → `ϑ`;
- in the proof of Lemma 3.2, `φ` → `f`;
- in Theorem 7.8, step 4, `φ` → `ω`;
- in §10.3, the generic `φ(D)` → `p(D)`.

**Moves.** «doblar» / «paso» → **twist move** / **split move**; «doblar map» → **twist map**.

**New §1.7, «Vocabulary, and why these names».** A table translates each of our words into its standard meaning, with the place where it is defined. Two paragraphs explain the names: «Why dance» and «Why dry and wet». The old §1.7 is now §1.8.

**Kept, with their double meanings declared in §1.6:** `D`, `K`, `T(·)`, `τ` and «window». `φ(x) = x + v_2(x)` and Kummer's `κ(a, b)` keep their names: they are standard and appear from §1.2 on.

## 8. The pdf [G §1.7, R §5.5]

The builder is `paper/md2html.py`, which documents its changes (1)–(10) in its header:
- a short formula (28 characters or fewer) never breaks across a line;
- mathematical alphanumerics, such as the Fraktur `𝔞`, `𝔅`, `𝔡`, are set in STIX Two Math;
- digit groups such as «14 560» are kept together;
- there is no hyphenation inside tables;
- an exponent or an index never breaks, and is never separated from its base;
- a long formula never ends a line at a comma;
- inside an exponent or an index the spaces are thin spaces;
- the end-of-proof mark ∎ never stands alone on a line;
- the two verification tables have fixed column widths;
- labels such as «Appendix A» are never split.

The ten defects of the reader's §5.5 were looked at one by one in the rebuilt pdf: all fixed. The whole pdf (43 pages) was looked at page by page. No line runs past the right margin (checked with `pdftotext -bbox` on every page).

## 9. Files

- `paper/THE_DANCING_SAND_THEOREM_v2.md` — md5 in `MANIFEST_md5.txt` after `hashes.sh`
- `paper/THE_DANCING_SAND_THEOREM_v2.pdf` (43 pages)
- `paper/THE_DANCING_SAND_THEOREM_v2.html`
- `paper/build_v2.sh`, `paper/md2html.py`
- `paper/v2_edits/` (`lib.py`, `part1.py` … `part11.py`)
- `paper/gate/` (the gates of version 2), `paper/gate_v1_record/` (those of version 1)
- `notes/QUERIES_CORRECCIONES_v2.md` (the searches behind the references and the credits)
