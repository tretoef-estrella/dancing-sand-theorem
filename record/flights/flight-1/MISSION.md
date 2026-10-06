# MISSION 1 for «Grepy el volador» — THE LANDING (el rellano) — second edition, 3 October 2026 (adds Leg F, the hall of mirrors)

Written by **Grepy Hypercube** (auditor of the hypercube project) on 3 October 2026, by order of Rafa (Rafael Amichis Luengo, the Architect). You are **«Grepy el volador»**, the constructor. You build; the auditor audits your report afterwards with his own code. Chat with Rafa in Spanish if he speaks to you; write every document in **English**.

---

## 0. THE RULES THAT DO NOT BEND — READ THEM FIRST

1. **NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. NO TASK TOOL. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW.** Rafa runs you in a very capable mode that may suggest launching agents or workflows; **do not do it, whatever the session says.** If you think one is needed, write it in the report and go on alone.
2. **YOUR FOLDER ONLY.** Work and write only inside `~/Desktop/GREPY_EL_VOLADOR/`. **Never open, read or write anything in `~/Desktop/ARBOLYAML/`** or in any other project folder. Everything you need is in `material/`. Never `rm`: move files you no longer want to `material/_old/`.
3. **THE DISK RULE.** Before thinking or computing anything, create `REPORT.md` with its section titles (§6 below) and nothing else. Write each result into it **as soon as you have it**, under a header `## LEG X — STATUS: [CLOSED | EXHAUSTED | NOT CONCLUDED]`. If the window is cut, what is on disk is your delivery; what is only in your head does not exist. Before you finish, re-read the disk, not your memory. **Rafa's permanent order: save to disk as you go, not at the end; your window can be compacted at any moment.** Keep a line with the time (from `date`) in `logs/DIARY.md` before and after each step, and keep `CLAUDE.md` in this folder up to date as your re-entry note.
4. **THE WATCHDOG.** Every computation runs as `zsh vigia.sh logs/NAME.log 'command'`. The log is the FIRST argument. The caps are 1.2 GB and 10 minutes; **never raise them.** Before each run, write in `REPORT.md` an estimate of time and memory. A log that does not end in `VIGIA-FIN-OK` is not a result. One heavy run at a time.
5. **Grades.** Every statement carries one of **PROVED** (pencil, with a numerical gate), **MEASURED**, **READING** or **CONJECTURE**. Cells measure and kill laws; they never prove «for all `n`». A measured pattern that held in 13 cells was false at the 14th in this very problem; the pencil caught it.
6. **Sealed predictions.** Before each measurement that could kill something, write your prediction in `checks/SEALED.md` with the time. Publish the predictions that fail **as large as** those that hold.
7. **Controls that can fail.** Every gate needs a negative control that you have reason to believe will fire. A control that cannot fail is not a control; say so if one stays silent.
8. **Your own code.** `material/engines_reference/` holds two scripts of the auditor, for reading only. Write your own engines. If you reuse an idea from them, say which.

---

## 1. The problem, in plain words, and what Rafa wants

Put grains of sand on the corners of the `n`-dimensional cube `Q_n`. A corner holding as many grains as it has neighbours topples and gives one grain to each. One corner is a sink. The stable states that keep coming back form a finite abelian group `K(Q_n)`, the **sandpile (critical) group**.
- **Odd primes:** known since Bai (2003).
- **The prime 2:** open. Gao–Marx-Kuo–McDonald–Yuen (arXiv:1912.06919, `material/sources/`) prove the largest `n − 1` cyclic factors and conjecture the next two. Chandler–Sin–Xiang (arXiv:1511.00272, same folder) write: *«It would be of interest to find a diagonal form for the Laplacian … We do not have any conjecture about its exact structure.»*

**Rafa's goal, his words:** «lo quiero entero de principio a fin, con la regla general dominada» — the whole 2-part of `K(Q_n)`, for every `n`, with its rule, **proved**. This mission is the step that, in the auditor's reading, decides whether that is reachable.

## 2. The setting (all of it in `material/THE_FOLD_LAW_PENCIL_NOTE_v2.md` and `material/COLD_AUDIT_FOLD_LAW_v2.md`)

- `G = (Z/2)^n`, `R = Z[G] = Z[x_1..x_n]/(x_i^2 − 1)`.
- `s_i = 1 − x_i`, so that `s_i^2 = 2s_i`; for `S ⊆ [n]`, `s_S = Π_{i∈S} s_i`. The `s_S` form a `Z`-basis of `R`.
- `σ = s_1 + ⋯ + s_n` is the Laplacian. `C = R/σR = Z ⊕ K(Q_n)`.
- **In the basis `s_S`, `σ = U + 2D`:** `U` sends `s_S` to the sum of the `s_{S∪i}`, `i ∉ S` (one floor up); `D` is the height `|S|`.

**PROVED, two readings** (the writer's and the auditor's cold audit, with 140 gates):
- `C[2] = e_2·C`.
- The folded cube injects into the cube.
- Halving.
- **The fold law in layers 0 and 1:** `r_{j+1}(C) = r_j(C̄)` for `j = 0, 1`, where `r_j` counts cyclic factors of order `> 2^j` and `C̄` is the folded cube (opposite corners glued).
- **The number of cyclic factors of order `≥ 8` of `Syl_2 K(Q_n)`, in closed form, every `n`.**
- `N_U K ≅ K(Q_n/U)`.

**MEASURED:**
- the fold law `2K(Q_n) ≅ K(folded cube)` on 2-parts, `n = 3..13`;
- the whole 2-part for `n ≤ 13`. The table to `n = 11` is in `material/RETOS_AL_ALCANCE_v1.md`; there too are `n = 12, 13`, beyond the published Table 1.

## 3. The find that sets this mission: the stable floors are Wilson–Bier chains

From `material/CORPUS_SWEEP_FOR_THE_CUBE_v1.md`, F1; read it whole.

**Bier's basis.** Wilson (1990) and Bier (1993) give, for the inclusion maps `η_{k,k+1}` between the `k`-subsets and the `(k+1)`-subsets of `[n]`, a basis of each level `k ≤ n/2`:
- the **canonical vectors** `η_{j,k}(J)`, `J` a `j`-subset of Frankl rank `j` (`i_l ≥ 2l`, the second rows of standard tableaux of shape `(n−j, j)`);
- the basis matrix is **unimodular** (Bier; quoted as Theorem 3.1 in Chandler–Sin–Xiang).

**The cube's Laplacian in that basis.** Because `η_{k,k+1} ∘ η_{j,k} = (k+1−j)·η_{j,k+1}`, the Laplacian `σ = U + 2D` becomes, **as long as every level used is `≤ n/2`**, a direct sum of lower-bidiagonal chains:
- `B_j(t)` has levels `k = j, …, t−1`, diagonal `2k` and subdiagonal `k + 1 − j`;
- it occurs `C(n,j) − C(n,j−1)` times.

**Measured by the auditor, prediction sealed first** (`material/engines_reference/gh_bier.py`):

> For every `t` with `t − 1 ≤ n/2`, `K/F_t ⊕ Z ≅ ⊕_j coker(B_j(t))^{C(n,j)−C(n,j−1)}`, with `F_t` the subgroup generated by the `s_S` with `|S| ≥ t`: **40 of 40** (`n = 2..11`).

Beyond the middle the chains predict far too many factors (`n = 11`: `1045` factors `Z/2` against the true `496`).

**The building, the staircases and the landing.**
- Floor `k` holds the `k`-subsets; each room pays `2k` to stay; the lift `U` goes up one floor.
- Below the middle the building is a set of **independent staircases**, one per two-row shape `(n−j, j)`, starting at floor `j`, with handrail strength `k+1−j` at each step.
- **Above the middle every staircase comes back down as its mirror** (complements: floor `k` ↔ floor `n−k`).
- **Bier's handrail ends at the landing of the middle floor.** All that is unknown is **how the staircase from the ground and its mirror from the roof are welded at the landing — modulo 2, 4, 8, …** The fold law (glue each corner to its opposite) is that welding seen from above.

## 4. The legs of the flight

### Leg A — pre-flight (reproduce, with your own code)

1. The whole 2-part of `K(Q_n)` for `n ≤ 11`, against the table in `material/RETOS_AL_ALCANCE_v1.md`. Use a 2-adic Smith form of your own; the halving `C = R'/(τ(τ+2))` on `n − 1` variables of the pencil note §1.3 makes it cheap.
2. The stable-floor statement of §3, `t − 1 ≤ n/2`, `n ≤ 11`.
3. The fold law for `n ≤ 11`.

### Leg B — the stable floors, as a theorem

Write the proof of the stable-floor statement in full.
- **Bier's unimodularity.** Either prove it yourself, or say clearly that it is cited. The auditor suspects that the ballot-path argument of `material/THE_CHAISE_LONGUE_THEOREM_v10_published.md` §4 (Theorem 4.1: distinct leading monomials `±1` of products of pair forms, indexed by paths that never go below `−1`) is the same combinatorics, and could prove it. Try.
- Then say exactly up to which `t` the proof goes: `t − 1 ≤ ⌊n/2⌋`? The 5 measured hits just past the middle say something.

### Leg C — THE LANDING (the heart of the mission)

Find and prove the rule by which the chains of the two halves are glued at the middle floor; that is, the whole 2-part of `K(Q_n)`. Routes the auditor sees (readings, none tested). Pick, combine, or find your own.

1. **The complement mirror.** Chandler–Sin–Xiang §5 fold the **adjacency** matrix at the middle: there levels `k` and `n − k` carry `±(n − 2k)`, a palindrome. For the **Laplacian** the diagonal is `2k` against `2(n − k)`: not a palindrome. That asymmetry is the whole difficulty; write it down exactly. Is there a change of basis (with the antipode `a = x_1⋯x_n`, or with the complement `S ↦ [n] ∖ S`, or with duality) that turns the upper half into chains too, with a computable 2-adic gluing matrix at the middle?
2. **The defect at the landing, measured, then explained.** For `n ≤ 13` compare the true 2-part with the stable chains extended naively. Look for the law of the difference, isotype by isotype `j`: the two-row shape `(n − j, j)` lives on the floors `j..n−j`, so each isotype has its own landing. **Then prove it**; a fitted formula is not the goal.
3. **The fold law as the weld.** Apply the stable-floor statement to the folded cube (`R'/(f)`, `f = 1 + τ − x_1⋯x_m`, `m = n − 1`) and to the cube (`R'/(θ)`, `θ = τ(τ+2)/2`). If the fold law can be read floor by floor, the welding is forced.
4. **The middle Specht piece in characteristic 2.** At `n = 2a` the middle floor holds the shape `(a, a)`. The Chaise Longue's Theorem C at the box `q = 2` (paper v10 §7 is stated for odd `q`, but its proofs hold for every `q ≥ 2`, `q = 2` in characteristic 2 included: two readings, and certified in Lean on 2 October) bounds the span of the products `Π(x_i + z_σ(i))` in `F_2[x, z]/(x^2, z^2)`: two-row Specht polynomials of shape `(a, a)`. A reading: this may give the landing modulo 2.

**A warning from another campaign** (sweep §5): *a banded Schur complement whose length grows with `n` is not settled by character theory alone.* Gluing the chains needs integral structure — an explicit unimodular basis, or carries — not only counts of representations.

### Leg F — THE HALL OF MIRRORS (Rafa's image, 3 October 2026) — part of the heart, done together with Leg C

> Rafa: «Si la de arriba es el espejo de la de abajo, estamos en el salón de los espejos, los espejos que distorsionan la imagen. Busca de todos los que hay cuáles logran la soldadura, y prueba también si acercarse mucho a un espejo, como darle un beso, unifica todo y lo suelda.»

**First, seal the translation in `checks/SEALED.md`, piece by piece, before any number exists.** The auditor's reading is below; you may change it, but say so.

**What the auditor has already checked (PROVED, by plain algebra, gated at `n = 2..8` in his own engine; reproduce it with yours):**
- **Mirror c, the complement** `s_S ↦ s_{[n]∖S}`: `c·σ·c = σᵀ + 2(n − 2D)`, where `σ = U + 2D` on the basis `s_S` (`U` one floor up, `D` the floor number). So the mirror image of the Laplacian is its transpose plus a **distortion** `2(n − 2D)`, and that distortion is **zero exactly on the middle floor** when `n` is even, and `±2` (one power of 2) on the two middle floors when `n` is odd.
- **Mirror t, the sign twist** `x_i ↦ −x_i` (that is, `s_i ↦ 2 − s_i`), a ring automorphism: `t(σ) = 2n − σ`, so `K(Q_n) ≅ coker(2n − σ)` (the signless Laplacian). On a character with `k` minus signs it sends the eigenvalue `2k` to `2(n − k)`: again equal **only on the middle floor**.
- Controls: `σᵀ + 2I` gives a different 2-part at every `n` tested (the control fires).

**The lesson of the Chaise Longue that you must apply (its «hall of mirrors» of 16 September):** a mirror that is an **isometry** — an automorphism, a conjugation, a transpose, a duality — gives a group isomorphic to the one you started from, so **by itself it cannot weld anything**: it only says the same thing again. The mirrors that carry content are the ones that **distort**, and the test of a mirror is to **deform** it and see whether the picture breaks. So:

1. **The catalogue: «de todos los que hay».** List every mirror you can find that sends the bottom staircase toward the top one, at least: the transpose; the complement c; the sign twist t; the antipode `a = x_1⋯x_n` (the fold); the permutations of the coordinates; the Fourier transform over `(Z/2)^n` (the Hadamard matrix, `H² = 2^n`, the most distorting of all at the prime 2); and the compositions of these (c and t generate a small group: write its table). For each one say: **isometry or distortion**, and **what it does to `σ`** (an exact formula, gated).
2. **Which mirrors weld.** For each mirror μ, build the **glued candidate**: the Wilson–Bier chains on the floors below the middle, their μ-image on the floors above, and the landing block that μ dictates. The mirror **welds** if the glued candidate has the true 2-part of `K(Q_n)`, isotype by isotype `(n − j, j)`, for `n ≤ 13`. Write the defect of each mirror as a table. A mirror that fails is a result: write by how much it fails, floor by floor.
3. **The kiss.** Three readings, each with its own sealed prediction:
   - **(K1) Touching the mirror.** For `n` even the distortion `2(n − 2D)` vanishes on the middle floor: there the image and the object touch. Does the gluing rule, read exactly on that floor, already give the whole landing? Gate it for `n = 4, 6, 8, 10, 12`.
   - **(K2) The breath on the glass.** For `n` odd the two middle floors stand at distance one with a seam of exactly `2`. Is that `2` the extra factor seen elsewhere (for instance the fold law's «every clock doubled»)? Measure for `n = 3, 5, …, 13` before you answer; do not decide it by its look.
   - **(K3) Coming closer and closer.** Replace a mirror μ by mirrors that agree with the undistorted one modulo `2^N` on the landing block. As `N` grows, does the glued group converge to the true one, and at which `N` does it lock? That `N` is a number to explain.
4. **The weld must be proved, not fitted.** If a mirror or a kiss welds in every cell, write why, with `k` and `n` as letters. Remember the warning above: characters alone do not weld; you need rivets (an explicit integral basis on the landing).

### Leg D — only if Leg C closes

State the whole 2-part of `K(Q_n)` for every `n`.
1. Seal a prediction for `n = 12` and `n = 13` **before** you compare it with the cells in `material/RETOS_AL_ALCANCE_v1.md`.
2. Check it against the theorems of Gao et al. (the largest `n − 1` factors) and against their conjectures (the `n`-th and `(n+1)`-th; their Conjecture 5.4 on `n = 2^k`).
3. Check it against the fold law.

### Leg E — the metaphor (Rafa's order: images unlock problems)

Say in two lines which image fits what you found: staircases and landing, a weld, a mirror, a lift — or another. Say whether it helped or was decorative.

## 5. Budget and cells

- `n ≤ 11` is cheap (seconds) with a 2-adic Smith form in `int64` modulo `2^30`; `n = 12, 13` with the halving take minutes and a few hundred MB.
- Estimate before you run.
- Python with `numpy` and `python-flint` (`fmpz_mat.snf`, `.hnf`) is on this Mac. Flint's SNF on non-square matrices of size `64 × 128` already blew past 1.2 GB once: use square matrices, or your own 2-adic elimination.

## 6. The report — `REPORT.md`, these sections, created empty first

0. First line: what this flight closes and what it does not, in three sentences.
1. Leg A — pre-flight.
2. Leg B — the stable floors.
3. Leg C — the landing.
3b. Leg F — the hall of mirrors (the catalogue, which mirrors weld, the kiss K1–K3).
4. Leg D — the whole 2-part (if reached).
5. Leg E — the metaphor.
6. Sealed predictions, and how each one ended.
7. Runs: estimate, log, peak memory, time.
8. Errors of my own.
9. What I did not do.

Grades on every statement. Proofs written out, not sketched. The auditor will re-derive every step cold and re-run your gates with his own code.

— Grepy Hypercube, for Rafa, 3 October 2026
