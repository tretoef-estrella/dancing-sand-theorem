# MISSION 4 — «Grepy el volador 4»: THE RENT AND THE GOLD (close the floor for every family)

Written by Grepy Hypercube, auditor of the hypercube project, 3 October 2026. You are a NEW constructor (Rafa's order: a fresh Claude for each mission, for hygiene). You never met the first three pilots; everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW** — whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §7, empty.
2. Every result goes into `REPORT.md` before you take the next step.
3. One line with the time (pasted from `date`, never guessed) in `logs/DIARY.md` before and after each step.
4. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted: re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, and go on from the last leg that is not CLOSED.
5. What is not on disk does not exist. **Rafa wants the story told one day: write in `REPORT.md` §9, in plain words, how each idea came.**

- You write only inside `~/Desktop/GREPY_EL_VOLADOR_4/` (scratch files too: never in a scratchpad or /tmp). You never open `~/Desktop/ARBOLYAML/` and you never use `rm`.
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'` (the log is the FIRST argument), run from this folder, with a written estimate of memory and time before it. Caps 1.2 GB and 10 minutes; they are not raised. A log that does not end in `VIGIA-FIN-OK` is not a result. Another session on this Mac builds Lean projects: one heavy job at a time.
- Grades on everything: **PROVED** (pencil, with a gate) / **MEASURED** / **READING** / **CONJECTURE**. Seal every prediction in `checks/SEALED.md` BEFORE you measure it; publish the failures in the same size of type. **A control must be able to fail.**
- Chat with Rafa in Spanish; documents in English.

## 1. STOP MEASURING HOUSES — Rafa's order for this flight

**«No sirve seguir midiendo el infinito. STOP medir más casas, no tiene fin, es un pozo; ya sabemos que hace falta una ley estructural.»**

Flight 3 closed the cube for every n ≤ 261 by a per-family machine check. **You do NOT check more families.** No λ = 262, no k = 8, no «the next family». Machines only to gate a pencil step on families that are already checked (λ ≤ 255), or to kill a candidate. A flight that comes back with more families and no structural law has failed.

## 2. Where the cube stands (read `material/FLIGHT3_REPORT.md` whole; flights 1–2 and the three audits as needed)

`K(Q_n)` is the sandpile group of the n-cube; its 2-part has been open since Bai (2003). Goal of the project: **the whole 2-part, for every n, proved.**

- **Theorem D** (flight 2; flight 3 removed every tilting citation): the 2-part is the Smith form of explicit `2^{|I|} × 2^{|I|}` matrices `M(λ, i)`, one family per λ (`λ + 1 = 2^k + Σ_{t∈I} 2^t`, dancers `D ⊆ I`).
- **Theorem O, the orphan** (flight 3, every family): every natural minor has a unique cheapest matching ⟹ `d_r ≤ U(r)` ⟹ `d_r ≤ Y(r)` (the pooled rule, the convex minorant).
- **Theorem A2** (|I| ≤ 2), P-R1 (odd λ), Lemmas F1–F4, St1, St2 (flight 3).
- **Open: the floor (ii).** For every family at once, every r-matching costs at least `Y(r)`. With Theorem O this gives `d_r = Y(r)` and the whole 2-part.

**The floor in its cleanest form (Lemma F4 of flight 3).** With `h_t = next(t) − t`, every arrow `D → D'` (`D' ⊆ D`) costs
  `ĉ(D, D') = R(D) + C(D') + γ(D∖D')`, with **`γ(Δ) = Σ_{u ∈ I∖Δ, u > min Δ} h_u ≥ 0`, the gaps the arrow skips**,
and the clocks are `x̂_D = R(D) + C(I∖D)`; `U(r)` = sum of the last r clocks (o-order). The natural matchings (rows L_r, columns F_r = their mirrors, no gap skipped) cost exactly `U(r)`.

## 3. Rafa's images for this flight (verbatim — translate them, seal the translation, say at the end which served)

**Image 1 — the rent.** «Oblígalos a que sea más barato que el alquiler; si por estructura es imposible, ahí tienes la respuesta. Esto pasó con Frobenius durante el Chaise Longue: le obligamos a hacer arruga, y como no podía, se convirtió en teorema.»

**Image 2 — the dancing gold.** «Las parejas al bailar rascan el suelo y salen pepitas de oro, que siempre valen más que el alquiler de la casa, o sea, si bailan, siempre vale más; cuanto más bailen, más valen. Es como vivir: si respiras hay oxidación, y si la hay hay envejecimiento; no se rejuvenece por estructura. O como el agua: siempre se evapora, no crece por sí misma, por estructura.»

## 4. The images, ALREADY MEASURED BY THE AUDITOR («mascadas»)

The auditor sealed the translation before measuring (`material/auditor_rent/gh_prediccion_sellada_alquiler.md`) and ran it on every family with λ ≤ 62 and |I| ≥ 2, α = 1..4, every m mod 2^k, both jump cases, P = 1..3, and i = 0: **16 224 cells, 1 723 of them with pooling** (`material/auditor_rent/gh_alquiler_62.log`, `gh_alquiler2_62.log`; engines in the same folder; they run from this folder).

**4.1 The rent (image 1) — an exact reformulation that KILLS THE POOLING (pencil, auditor; re-derive it).**
- The rent is an integer s that every couple (every matched pair, loops included) pays. Under rent s a partial matching m pays `Σ_{(D,D')∈m} (ĉ(D,D') − s)`; the best natural house pays `min_r (U(r) − s·r)`.
- `T(r)` (cheapest r-matching) is convex in r (min-cost flow). `Y` is convex with integer increments. So **`T ≥ Y` for every r ⟺ for every integer s, `min_r (T(r) − s r) ≥ min_r (Y(r) − s r)`**, and **`min_r(Y(r) − s r) = min_r(U(r) − s r)`** (a convex minorant has the same Legendre transform; with integer s the integer splitting of the pooled values changes nothing).
- ⟹ **THE FLOOR ⟺ «under every rent, no partial matching is cheaper than the best natural house».** The pooling (PAVA) disappears from the statement. Measured: the two forms agree in 16 224 of 16 224 cells.
- Equivalently (LP duality, the bipartite matching polytope is integral): **for every s there are integer «rent receipts»**, potentials `p_D ≤ 0` on rows and `q_{D'} ≤ 0` on columns with `p_D + q_{D'} ≤ ĉ(D, D') − s` on every arrow, and `Σ p + Σ q = min_r (U(r) − s r)`. Writing those receipts in closed form, for every s, IS a proof of the floor.

**4.2 The gold (image 2) — measured, every cell.** A couple **dances** when its arrow skips a gap (`γ > 0`); its nugget is γ. Discount part of the gold and ask whether the floor (in rent form) still holds:

| discount on each arrow | cells where the floor FAILS (of 16 224) |
|---|---|
| none | 0 |
| **1 coin per dancing couple** | **0** |
| 2 coins per dancing couple | 13 192 |
| **half the gold, ⌈γ/2⌉ (and ⌊γ/2⌋)** | **0** |
| γ − 1 | 27 |
| all the gold, γ | 741 — every one with pooling |
| only walking allowed (arrows with γ = 0 and loops) | 0 |

Read as Rafa's image:
- **«Siempre valen más que el alquiler»:** every dancing couple carries at least one coin above the rent, and **half of its gold already pays it** — the gold is worth at least twice what it must pay. Two coins per couple is too much (13 192 failures): the uniform margin is exactly one.
- **«Cuanto más bailen, más valen»:** because the margin is per couple, the slack of a matching grows with the number of dancing couples: excess ≥ number of dancers.
- **The gold is needed** (all gold removed: 741 failures, all in pooled cells) — as flight 3 found (S4): the proof must use the ruler's growth `α·2^t`. **The gold cannot be ignored; only half of it can.**
- **Walking alone never beats the rent** (0 failures): the rows-and-columns part `Σ R + Σ C` against the houses is a statement of its own.

## 5. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — the second reading owed by flight 3 (budget 15 %).** Write out in full the case table of Theorem A2 (flight 3 §2, A.3: «each inequality written out in my working notes») and re-read Lemma St2 cold. Mark each CORRECT / GAP / ERROR.

**Leg A — the rent theorem (image 1).** Prove, for every family, every shift and every α ≥ 1: **under every integer rent s, no partial matching is cheaper than the best natural house.** Follow Rafa's image literally: assume a matching cheaper than the rent, take a MINIMAL one (fewest dancers, then smallest |I|, or smallest r — choose and say why), and show it must make a «wrinkle» it structurally cannot make. Tools in the folder:
- the lowest-digit peeling (F2) and König's edge colouring (F3) — F3 already closes the short-run case τ ≥ 0;
- the top-digit induction of Theorem O (B.3–B.4) and strict subadditivity;
- the receipts of 4.1 (assignment duality, Egerváry potentials: not in the corpus, classical);
- **Gold 2** (`material/GOLD_FOR_THE_FLOOR_v1.md`): the Chaise strengthened its statement to every down-set so that the induction closes; **here the measured strengthening is the half-gold statement of Leg B** — a stronger hypothesis is easier to carry through an induction.
- **Gold 1:** the floor is the SAFE direction of the tropical lens (a sum cannot be cheaper than its cheapest term); no cancellation argument is needed.

**Leg B — the gold (image 2).** Prove the two measured statements, for every family:
- **(G½)** the rent form holds with every arrow discounted by `⌈γ/2⌉`;
- **(G1)** the rent form holds with every dancing arrow discounted by 1.
Explain why exactly half: the König doubling of F3 halves a matching into two; the gaps `h_u` of the ruler are tied to the positions (`τ_t ∈ [1 − α2^t, h_t − α2^t]`). **Water evaporates, breath oxidizes: show the gold is MONOTONE** — removing one dancing couple from a matching never raises its excess over the rent by more than that couple's coin. If (G½) is the right induction hypothesis for Leg A, say so and use it.

**Leg C — assembly and trophies.** If A and B close: the floor for every family ⟹ with Theorem O, Theorem D, P-R1 and A2: **the whole 2-part of `K(Q_n)` for every n**, with every dependency named, and Gao et al. Conj. 4.14, 5.4 and the poster's (n+1)-th factor for every n. If not, say exactly which step is missing, with the smallest family (λ ≤ 255) where its gate is visible.

**Kill criteria.** If (G1) or (G½) fails in a cell of a family λ ≤ 255, that is the first line of your report (it is allowed to gate them on families up to λ = 255 — already checked — but never beyond).

## 6. What you must not do
- Do not check new families or new cubes («más casas»). It is a well with no bottom.
- Do not claim novelty without saying what you read in the original (`material/sources/`; an automatic summary is not a reading).
- Do not touch anything outside this folder.

## 7. Sections of REPORT.md (create them empty first)
0. First line — what this flight closes and what it does not
1. Leg 0 — second reading (A2 table, St2)
2. Leg A — the rent
3. Leg B — the gold
4. Leg C — assembly and trophies
5. Rafa's images — which served
6. Sealed predictions, hits and failures
7. My errors
8. Files with md5
9. The story of this flight, in plain words

Budget: each leg, write the estimate in `REPORT.md` before starting it; ten minutes with no traction ⟹ stop, write what you have, mark it AGOTADO. Keep the last fifth of your time for writing.
