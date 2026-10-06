# MISSION 2 — «Grepy el volador 2»: THE TWO MOVES (prove the closed rule of the cube of sand)

Written by Grepy Hypercube, auditor of the hypercube project, 3 October 2026. You are a NEW constructor (Rafa's order: a fresh Claude for each mission, for hygiene). You never met the first pilot; everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW** — whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §6, empty.
2. Every result goes into `REPORT.md` before you take the next step.
3. One line with the time (`date`) in `logs/DIARY.md` before and after each step.
4. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted: re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, and go on from the last leg that is not CLOSED.
5. What is not on disk does not exist.

- You write only inside `~/Desktop/GREPY_EL_VOLADOR_2/`. You never open `~/Desktop/ARBOLYAML/` and you never use `rm`.
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'` (the log is the FIRST argument), with a written estimate of memory and time before it. Caps 1.2 GB and 10 minutes; they are not raised. A log that does not end in `VIGIA-FIN-OK` is not a result. Another session on this Mac builds Lean projects: run one heavy job at a time.
- Grades on everything: **PROVED** (pencil, with a gate) / **MEASURED** / **READING** / **CONJECTURE**. Seal every prediction in `checks/SEALED.md` BEFORE you measure it, and publish the ones that fail in the same size of type.
- Chat with Rafa in Spanish; documents in English.

## 1. The object

`K(Q_n)` is the sandpile (critical) group of the n-cube. Its 2-part is the open problem (Bai 2003; Chandler–Sin–Xiang; Gao et al., arXiv:1912.06919). The goal of the project is **the whole 2-part, for every n, proved**.

The first flight (`material/FLIGHT1_REPORT.md`, read it whole; its engines are in `material/flight1_engines/`) reduced the problem to this:

- **Dictionary.** `Z[(Z/2)^n] ≅ V^{⊗n}` (V the natural module of SL_2 over Z); σ = U + 2D becomes `F + n − H`. On any module with weights ≤ c of the same parity put `σ_c = F + (c − H)`, and more generally `σ^(α) = F + 2^α·(floor)`.
- **Theorem RT** (proved modulo standard tilting theory): `Syl_2 K(Q_n) ⊕ Z_2 ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}`, with `X(λ, i) = coker(F + λ − H + 2i)` on the indecomposable tilting lattice `T_{Z_2}(λ)` and `m_λ(n)` the multiplicity of T(λ) in `V^{⊗n}` over F_2.
- **Theorem S** (proved): the Steinberg families `λ = 2^k − 1` in closed form, by halving a bidiagonal matrix.
- **Theorem E** (proved): for odd ν, `X(ν+1, i) ≅ coker(τ(τ+2))` on `T(ν)`, `τ = F + ν − H + 2i`.
- **Conjecture W** (the closed rule, `material/flight1_engines/rule.py`): small clocks `⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}}` plus `2^{|I|}` big clocks given by «rooms over handrail» `B(μ, j)`, transfers `next(t) − t`, and pooling of adjacent violators. Held in every test: 1271/1271 cells, n = 33..40 sealed before computing, 294 large-model cells, all known theorems to n = 128 — and the auditor re-checked it against three engines that are not the pilot's (whole group n = 2..13, layers at n = 14, 15, 16): 15/15.
- **P-R1** (MEASURED 276/276, odd λ ≤ 39, α = 1, 2, j ≤ 20): for `λ = 2λ₁ + 1`,
  `X^(α)(λ, j) = (dim T(λ)/2 units) ⊕ 2·X^(2α)(λ₁, ⌈j/2⌉)`.

**With P-R1 and its even analogue, every family is reached from T(0) by two moves, λ → 2λ+1 and λ → λ+1, and Conjecture W would follow.** That is your mission.

## 2. Rafa's images (translate each one piece by piece, seal the translation on disk BEFORE measuring, and say at the end which one served and which was decorative)

1. «En el equilibrio del conjunto hay un premio para cada cubo, y es potencia de dos porque no puede sobrar nada, ni faltar.»
2. «Binario, o está o no está, en secado o en mojado, y en el doble de horas.» — the first pilot turned this into the proof of Theorem S: each halving keeps half the floors, doubles every clock and squares what the rooms pay.
3. «Si la de arriba es el espejo de la de abajo, estamos en el salón de los espejos.» — the weld is the piece the transpose mirror leaves fixed (the tilting module).
4. **New for you — the two moves are two steps of a dance:** «doblar» (λ → 2λ+1: fold the room in two, the payment doubles) and «dar un paso» (λ → λ+1: put one more pair of feet, the operator becomes τ(τ+2)). The whole cube is a dance from T(0) with these two steps. Prove that each step does to the clocks exactly what the closed rule says.

## 3. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — second reading of the proved theorems (budget: 20 % of your time).** Read cold, line by line, Theorems Z, B, RT, S, E and the case λ = 2 of `FLIGHT1_REPORT.md`. For each, write in your own words the step that carries the weight and mark CORRECT / GAP / ERROR. For RT, say exactly which facts of tilting theory over Z_2 are cited (Jantzen II.E) and whether they apply at p = 2 over the 2-adic integers. Re-run two of the pilot's gates with your own code. This is the second reading the project needs: do not stamp.

**Leg A — P-R1 as a theorem (the odd step, «doblar»).** Over F_2, `T(2λ₁+1) = V ⊗ T(λ₁)^{[1]}` (Donkin). Over Z_2 there is no Frobenius twist, so you need an INTEGRAL statement: an explicit Z_2-lattice model of `T_{Z_2}(2λ₁+1)` (the tensor products of Steinberg lattices `St_k` are explicit tilting lattices and contain each T(λ) once at their top weight — see C.1 of the report), on which `σ^(α)` has `dim/2` unit pivots pairing the two vectors of V, and what is left is `2·σ^(2α)` on a lattice isomorphic to `T_{Z_2}(λ₁)` at shift `⌈j/2⌉`. Theorem S is the special case λ₁ = 2^{k−1} − 1: start from its proof. Gate: your proof against the pilot's 276 cells and new ones you seal (λ up to 63).

**Leg B — the even step («dar un paso»).** By Theorem E the even family `ν + 1` is `coker(τ(τ+2))` on the odd family `T(ν)`. Formulate and prove the analogue of P-R1 for the operator `τ(τ+2)` (equivalently `2θ`, θ = τ(τ+2)/2) on `T(2λ₁ + 1)`. Seal the formulation before measuring. If the natural statement fails, say where, and find the one that holds.

**Leg C — the rule follows from the two steps.** Show that the closed rule of `rule.py` (small clocks, rooms over handrail, transfers `next(t) − t`, pooling) is the unique solution of the recursion given by Legs A and B with base T(0). The pooling of adjacent violators should come out of the Smith form of the merged chains; the first pilot's failed P-H1 (91/615 cells, exactly where clocks pool) shows that a naive shift is not enough. Prove the layer statement P-X1 (number of factors of exponent ≥ a is dim T(λ)/2^a for a ≤ k) along the way.

**Leg D — assembly and trophies.** If A, B and C close: write the theorem of the whole 2-part of `K(Q_n)` for every n, with every dependency named. Then, as corollaries, check which open statements of Gao et al. (arXiv:1912.06919: Conjectures 4.14 and 5.4) and of Reiner's poster (the (n+1)-th factor) become theorems. If A, B or C do not close, say exactly which step is missing, with the smallest cell where it is visible.

**Kill criteria.** If P-R1 fails in a sealed new cell, stop Leg A and report the cell. If Conjecture W fails anywhere, that is the first line of the report.

## 4. What you must not do
- Do not recompute the group for larger n as «progress»: more cells are not a proof. Machines only to gate a pencil step or to kill a candidate.
- Do not claim novelty without saying what you read in the original (the sources are in `material/sources/`; an automatic summary is not a reading).
- Do not touch anything outside this folder.

## 5. Budget
Each leg: write the estimate in `REPORT.md` before starting it; if ten minutes pass with no traction, stop, write what you have and mark it AGOTADO. Keep the last fifth of your time for writing.

## 6. Sections of REPORT.md (create them empty first)
0. First line — what this flight closes and what it does not
1. Leg 0 — second reading of the proved theorems
2. Leg A — the odd step
3. Leg B — the even step
4. Leg C — the rule from the two steps
5. Leg D — assembly and trophies
6. Rafa's images — which served
7. Sealed predictions, hits and failures
8. My errors
9. Files with md5

At the end, in the first line of the report: what this flight closes and what it does not.
