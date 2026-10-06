# MISSION 3 — «Grepy el volador 3»: THE ORPHAN (close the cube of sand)

Written by Grepy Hypercube, auditor of the hypercube project, 3 October 2026. You are a NEW constructor (Rafa's order: a fresh Claude for each mission, for hygiene). You never met the first two pilots; everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW** — whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §7, empty.
2. Every result goes into `REPORT.md` before you take the next step.
3. One line with the time (pasted from `date`, never guessed) in `logs/DIARY.md` before and after each step.
4. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted: re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, and go on from the last leg that is not CLOSED.
5. What is not on disk does not exist. **Rafa wants the story told one day: write in `REPORT.md` §9, in plain words, how each idea came.**

- You write only inside `~/Desktop/GREPY_EL_VOLADOR_3/`. You never open `~/Desktop/ARBOLYAML/` and you never use `rm`.
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'` (the log is the FIRST argument), with a written estimate of memory and time before it. Caps 1.2 GB and 10 minutes; they are not raised. A log that does not end in `VIGIA-FIN-OK` is not a result. Another session on this Mac builds Lean projects: one heavy job at a time.
- Grades on everything: **PROVED** (pencil, with a gate) / **MEASURED** / **READING** / **CONJECTURE**. Seal every prediction in `checks/SEALED.md` BEFORE you measure it; publish the failures in the same size of type. **A control must be able to fail** (the auditor's own first control this morning multiplied a coefficient by −3: a unit, which cannot change a 2-adic Smith form — it could not fire).
- Chat with Rafa in Spanish; documents in English.

## 1. Where the cube stands (read `material/FLIGHT1_REPORT.md` and `material/FLIGHT2_REPORT.md` whole)

`K(Q_n)` is the sandpile group of the n-cube; its 2-part has been open since Bai (2003). Goal of the project: **the whole 2-part, for every n, proved.**

After two flights, by one hand each, with the auditor's positive first pass (`material/AUDIT_FIRST_PASS_FLIGHT_1.md`, `…_FLIGHT_2.md`):

- **Theorem RT** (tilting splitting) and the flight-1 theorems Z, B, S, E, λ = 2 now have two readings.
- **Flight 2** proved by one hand: the integral «doblar» functor Φ with `Φ(T(l)) = T(2l+1)`; **P-R1** (the odd step); the even step as two coupled dancers; the dance recursion; the coefficient algebra `q_{t+1} = q_t² − [t ∈ I] y_t q_t`; the deficit law `v_2(a_k(Δ)) = k − |Δ| − min Δ`; the small clocks P-X1; and

  **Theorem D.** `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ 2^k·coker M(λ, (n−λ)/2) ]^{m_λ(n)}`, with `λ + 1 = 2^k + Σ_{t∈I} 2^t`, `o_D = Σ_{t∈D} 2^t` and, for `D' ⊆ D ⊆ I`,
  `M(λ, i)_{DD'} = −2^{1−2^k} · a_k(D∖D') · 2^{o_D − o_{D'}} · ∏_{d=o_D}^{o_{D'}+2^k−1} 2(i+d)` (0 if `D' ⊄ D`).

  **The auditor checked Theorem D as printed with his own code** (own multiplicities, own recursion, own Smith form; `material/auditor_engine.py`): the whole group n = 2..13 and the layers at n = 14, 15, 16, 15/15.

- **The one open step, (C-b):** for `|I| ≥ 2`, `Smith(M(λ, i))` equals the rule's pooled big clocks minus k (Conjecture W). Measured everywhere (4352/4352; tropical 882/882; natural minors with a unique optimal matching 2632/2632). It is FALSE for weights that do not come from the 2-adic ruler `w(d) = α − 1 + v_2(i + d)` (flight 2, C.6): **the proof must use the ruler.**

- **The smallest open cell is n = 6, λ = 6, i = 0** (`7 = 4 + 2 + 1`, k = 2, I = {0, 1}, a 4×4 matrix). The auditor wrote out `M(6, i)` for i = 0, 1, 2 with valuations in `material/THE_FIRST_OPEN_CELL_M6_by_auditor.txt` (rows and columns in the order ∅, {0}, {1}, {0,1}). For i = 1: Smith exponents (3, 3, 5, 5); the natural 2×2 minor (rows {1}, {0,1}; columns ∅, {0}) is `24·40`, one term: the orphan in person.

**What would close (C-b)** (flight 2 §4 end; the auditor agrees, `AUDIT_FIRST_PASS_FLIGHT_2.md` §4): d_r = the r-th determinantal divisor of M (Smith partial sums are convex).
- (i) **No cancellation:** every natural minor `M[L_r, F_r]` (last r rows, first r columns) has a unique term of minimal valuation ⟹ `d_r ≤ U(r)` (the unpooled rule) ⟹ by convexity `d_r ≤ Y(r)`, the greatest convex minorant = the pooled rule.
- (ii) **Floor:** every r-matching inside the support of M costs at least Y(r) (a TROPICAL statement: then every r×r minor has valuation ≥ Y(r)).
- Then `d_r = Y(r)` for every r: Conjecture W is a theorem, and the cube is closed.

Both (i) and (ii) are assignment problems on the explicit weights `v(M_{DD'}) = ρ_D + κ_{D'} + δ(D∖D')`, `δ(Δ) = k − |Δ| − min Δ`, with the ruler inside ρ, κ (flight 2, C.5–C.6).

## 2. Rafa's images — translate each one piece by piece, seal the translation BEFORE measuring, and say at the end which served and which was decorative

The old ones (they served in flights 1–2):
1. «En el equilibrio del conjunto hay un premio para cada cubo, y es potencia de dos porque no puede sobrar nada, ni faltar.» (Flight 2: «el equilibrio» = the pooling; it is exactly what is still open.)
2. «Binario, o está o no está, en secado o en mojado, y en el doble de horas.» (Became Theorem S and the functor Φ.)
3. «Si la de arriba es el espejo de la de abajo, estamos en el salón de los espejos.» (Became the tilting module and the mirror `I ∖ D` of each dancer.)
4. The dance: «doblar» and «dar un paso». (Became Theorem D.)

**The new ones, each with the gold Rafa attached to it** (Grepy Mandalay brought the gold from the corpus; Rafa put the images; the auditor checked where each piece is):

5. **The orphan.** Gold: the ballot paths of the Chaise Longue (`material/gold/THE_CHAISE_LONGUE_THEOREM_v11_UNRELEASED.md`, Theorem 4.1, line ~278): there, independence is proved because each product has a unique leading monomial. Same idea with another order: instead of the monomial order, the 2-adic valuation. «A minor has a unique term of minimal valuation» is exactly the no-cancellation (i).
   > Rafa: «esto suena a que un niño es huérfano de padre o madre, y el que le queda se ocupa de todo, así no hace falta cargarse a nadie, ya se murió solo».
   (Auditor's reading: when the optimal matching is unique, nobody has to cancel anybody; the one term that survives carries the whole valuation. Flight 2 measured the orphan 2632/2632; you must PROVE it.)

6. **The two traffic lights.** Gold: Lindström–Gessel–Viennot — a minor of a path matrix is a signed sum over families of non-crossing paths; if exactly one family has minimal valuation, the room is closed. The corpus points to it in `material/gold/LGV_pointer_from_catalogue_v524_lines1206-1207.md` (Lindström 1973; Gessel–Viennot 1985; Krattenthaler, arXiv:1503.05930 §10.13; Lee, arXiv:2112.06115). **Warning from the auditor: most hits of «Gessel» in the corpus are Gessel–Monsky (Hilbert–Kunz theory), a different object — a name collision. The corpus has no LGV work of its own.**
   > Rafa: «Hay que encontrar a esa familia del niño huérfano en los pueblos con dos semáforos.»
   (Auditor's READING, not checked: the two traffic lights are the two dance steps. By flight 2 C.7.4, the even step is a conjugation `L^{−1} diag(σ_A, σ_C) L` by an elementary gluing; iterating, M is a diagonal conjugated by a product of elementary 2×2 gluings — a planar network. Build that network explicitly and read the minors of M as non-crossing path families.)

7. **The rights of the minors.** Gold: Cauchy–Binet with Vandermonde factors (Chaise reports 107–111, `material/gold/chaise_reports/`): minors written as products that cannot vanish.
   > Rafa: «Los derechos de los menores son inquebrantables y no se pueden anular, son prioridad y el resto cuelga de esos derechos.»
   (Auditor's READING: flight 2 C.4(iii) gives `M = −2^{1−2^k} X'^{−1} A Y'` with X', Y' diagonal and A = multiplication by `q_k = −∏_{t<k}(q_t − y_t)` in `Z[y_t]/(y_t²)`: a product of simple multiplication operators, so Cauchy–Binet expands every minor of A over the factors.)

8. **The salsa.** Gold: Lemma 9.10 of the Chaise (`…v11_UNRELEASED.md`, line ~1099): at the prime 2, `(t−1)^q = t^q − 1` and the map θ (the coefficient of `t^0`) lowers one variable without losing dimension — the same gesture as «pairing the two vectors of V» in «doblar».
   > Rafa: «Es como el baile de salsa, paso de lado a lado y delante y detrás.»
   (Flight 2 C.7.1 already removes the lowest digit: «side to side» = the pair (D1, D1 ∪ {0}); «forward and back» = the two scalings, rows and columns, mirror of each other up to one jump e* (C.6).)

9. **Tilting read in the original, and the dead routes.** Gold: Jantzen (screenshots of II.1.19, II.2.13, II.4.16 in `material/gold/tilting_originals/capturas_jantzen*/`; how they were fixed: `HOW_THE_CITATIONS_WERE_FIXED_regla177.md`), Mathieu 1990 (`ASENS_1990…pdf`, Theorem 1(1)), Hashimoto. And the Chaise's own work with `St^{⊗n}` at p = 3 (reports 68–74) — the same frame as the cube at p = 2. **Dead routes there — do not retry:** Kolchin (a unipotent group on a non-zero module has non-zero invariants: «the invariants of the quotient vanish» is never true); `H¹(G_a, k)` is infinite-dimensional in characteristic p; the box is free over G₁ but NOT over G₂.
   **Warning from the auditor: Jantzen's chapter II.4 is written over a FIELD («Let k be a field throughout this chapter»).** Flight 2 cites «II.4.13 and II.B … for any Noetherian base ring» for the integral (Z_2) facts used by RT and Φ. Check exactly where the base-ring versions are (Jantzen II.B, Andersen, Donkin) — this is Leg 0.

## 3. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — second reading of flight 2 (budget 15 %).** Read cold, line by line: A.1 (Φ), A.2 (P-R1), B.1, C.0, C.1, C.4, D.1 (Theorem D). For each, the step that carries the weight in your words, and CORRECT / GAP / ERROR. Fix the integral citations (warning of image 9). Re-run two of the pilot's gates with your own code. No stamps.

**Leg A — the first open family, by hand: |I| = 2 (the 4×4).** Every λ with exactly two lower binary digits, every shift i, every α. Write M(λ, i) in closed form (4×4, lower triangular for the Boolean order), and prove `Smith(M) = rule − k` by (i) + (ii), using the ruler. Flight 2 C.7.2 found that the optimal rows/columns take only four shapes for |I| = 2 — prove that. Start from n = 6, λ = 6. This leg alone, closed, is a new theorem: every family with at most two lower digits.

**Leg B — the orphan in general: (i) no cancellation.** Prove that every natural minor `M[L_r, F_r]` has a unique term of minimal valuation, for every |I|. Routes in order of the gold: (5) a unique «leading» matching, as the ballot paths; (6) LGV on the gluing network; (7) Cauchy–Binet on A = ∏ (multiplication factors). Flight 2 C.5 fact 2 gives the identity `Φ(L_r, F_r) = Σ_{D∈L_r} ε(D)` (measured 798/798) — prove it too.

**Leg C — the floor: (ii).** Every r-matching in the support costs at least Y(r). The statement is false for non-realisable weights (C.6), so use the ruler: over an aligned dyadic block `[y, y + 2^t)` the sum of w is `2^t α − 1 + v_2(⌈i/2^t⌉ + y/2^t)`; «v(x) ≠ v(x + 2^e) forces both ≥ e» (the |I| = 1 proof, C.1). Flight 2's suggestion (C.7.4): read it as Hodge versus Newton for a diagonal operator on a glued lattice (Mazur's inequality: the Hodge polygon lies below the Newton polygon, same endpoints).

**Leg D — assembly and trophies.** If A, B, C close: write the theorem of the whole 2-part of K(Q_n) for every n, every dependency named. Then the trophies, each as a corollary with its proof: Gao–Marx–Kuo–McDonald–Yuen (arXiv:1912.06919, in `material/sources/`) Conjecture 4.14 (the n-th factor) and Conjecture 5.4 (`Syl_2 K(Q_{2^k}) ≅ Syl_2 K(Q_{2^k−1})² × Z/2^{2^k+k−1}`); the JMM poster's (n+1)-th factor; and the fold law (`Syl_2 K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl_2 K(folded cube), every exponent +1]`, `material/sources` and flight 1, measured to n = 32). If something does not close, say which step, with the smallest cell where it is visible.

**Kill criteria.** If Conjecture W fails in any sealed cell, that is the first line of the report. If the orphan has a twin (two terms of equal minimal valuation that cancel) in some natural minor, stop Leg B and report the cell.

## 4. What you must not do
- No more cells as «progress». Machines only to gate a pencil step or to kill a candidate.
- No novelty claimed without saying what you read in the original (`pdftotext`, then read; an automatic summary is not a reading). The functor Φ, Theorem D and the deficit law may exist in the literature on integral Frobenius twists or tilting modules for SL_2 at p = 2: if you search, say what you found.
- Nothing outside this folder.

## 5. Budget
Write the estimate of each leg in `REPORT.md` before starting it; if ten minutes pass with no traction, stop, write what you have and mark AGOTADO. The last fifth of your time is only for writing.

## 6. The auditor will help
The auditor's engine (`material/auditor_engine.py`, run `python3 material/auditor_engine.py 6 8`) computes M(λ, i), its Smith form and the cube for any n from Theorem D, independently of flight 2's code. Use it as a second engine for your gates.

## 7. Sections of REPORT.md (create them empty first)
0. First line — what this flight closes and what it does not
1. Leg 0 — second reading of flight 2
2. Leg A — the 4×4 (|I| = 2)
3. Leg B — the orphan (no cancellation)
4. Leg C — the floor
5. Leg D — assembly and trophies
6. Rafa's images — which served
7. Sealed predictions, hits and failures
8. My errors
9. The story of this flight, in plain words (for Rafa's account of how it was done)
10. Files with md5

At the end, in the first line of the report: what this flight closes and what it does not.
