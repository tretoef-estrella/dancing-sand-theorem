# MISSION 8 (version 2) — «Grepy el volador 8»: THE DRY AND WET LAW FOR EVERY n — the drain, the owner, the U

Written by Grepy Bross, the auditor of the hypercube project, on 4 October 2026 (evening). You are a NEW constructor: Rafa orders a fresh Claude for each mission. You never met the seven pilots before you. Everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §8, empty.
2. Every lemma goes into `REPORT.md` the moment you have it, before you look for the next one.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Write each leg's estimate in `REPORT.md` BEFORE you start the leg, and each run's estimate (memory and time) BEFORE the run.
5. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each leg. If your window is compacted, re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, then go on from the last leg that is not CLOSED.
6. What is not on disk does not exist. A write that fails must not be reported as done: check the file, then write the diary line (flight 7's E2).
7. Tell in `REPORT.md` §8, in plain words, how each idea came: Rafa wants the story.

**Where you work**
- Write only inside `~/Desktop/GREPY_EL_VOLADOR_8/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`. Never use `rm`. Never read a Desktop screenshot.
- `material/` is read-only. Copy any engine you run into `engines/` and fix its paths there.

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Integers and exact fractions only.

**Grades:** **PROVED** (pencil, with a gate), **MEASURED**, **READING**, **CONJECTURE**.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds.
- Publish failures in the same size of type as hits.
- A control must be able to fail; say which of yours did.
- Do not mark PROVED what you have only sketched (flight 7's E4).

Chat with Rafa in Spanish; documents in English.

## 1. Where the cube stands

**Closed (read `material/AUDIT_FLIGHT_4.md`, `material/AUDIT_FLIGHT_6.md`):**
- **The Dancing Sand Theorem.** The whole Syl₂ K(Q_n) is known for every n by a closed rule (flights 1–4):
  **Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}**, X(λ, i) = coker(τ_i) on the tilting lattice T(λ) over Z₂, τ_i = F + 2(D + i).
  The cokernel of every payment operator coker(F + 2^α(D + c)) on T(l) is given by the rule, for **every α ≥ 1** (flight 4b, Conjecture W).
- **The trophies:** Bai's counts, Gao et al. 4.14 and 5.4 for every k, the poster's (n+1)-th factor (flights 5–6).

**The second theorem, «The Dry and Wet Law»** (the fold law): **2K(Q_n) ≅ K̄(n) on 2-parts**, K̄(n) the sandpile group of the folded cube.
- Lemma RT̄ (flight 6): **Syl₂ K̄(n) ⊕ Z₂ ≅ ⊕_λ X̄(λ, i)^{m_λ(n)}**, X̄(λ, i) = T(λ)/(τ_i T + (a − 1)T), a = (−1)^{D+i}·exp F.
- So the law for n follows from the **family law X̄(λ, i) ≅ 2X(λ, i)** for every family and shift (flight 6 §4.2; flight 7 §3.1).
- **PROVED for every n ≤ 100** (flight 7's Theorem C₇, every cell computed twice by independent codes). **For every n it is OPEN.**
- **Rafa's decision: it WILL be closed for every n. There is no fallback to a conjecture.** Your job is to close it. If you do not, you report exactly how far you got; you do not propose to print it as a conjecture.

**What flight 7 proved and measured (read `material/flight7/FLIGHT7_REPORT.md` §2 and `material/AUDIT_FLIGHT_7.md`):**
- **Lemma A0 (PROVED):** X(λ, i)[2] = e₂X with e₂ = τ(τ − 2)/2, so 2X ≅ T/(τ, e₂)T. The family law reads T/(τ, e₂)T ≅ T/(τ, a − 1)T.
- **Lemma H-odd (PROVED):** for λ = 2λ₁ + 1, N = T(λ₁), any shift j ≥ 0, ε = (−1)^j:
  X̄(λ, j) ≅ coker(2(2D + j) + (Ch − ε)·Sh⁻¹) on N, where Ch = Σ_s F^(s)/(2s−1)!! and Sh = Σ_s F^(s)/(2s+1)!!.
  - (Ch − 1)Sh⁻¹ = u·tanh(u/2) and (Ch + 1)Sh⁻¹ = u·coth(u/2), with u² = 2F.
  - And 2X(λ, j) ≅ coker(F + 4(D + ⌈j/2⌉)) on N (flight 2's P-R1).
  - **So the odd families are exactly (P):** coker(F + 4(D + c) + Σ_{m≥2} ζ_m F^(m)) ≅ coker(F + 4(D + c)) on every T(l), for the constant ζ of those two series, after a floor scaling that makes the F-coefficient 1.
- **Lemma H-even (PROVED):** for λ = ν + 1, ν odd, X̄(λ, i) ≅ coker(1 + τ − a) on T(ν), and 2X(λ, i) ≅ coker(τ(τ + 2)/2) on T(ν), at the same shift i.
- **The safe class PL\* (MEASURED, 3 600 trials):** on T(l) with α ≥ 2, adding Σ_{m≥2} φ_m(D)F^(m) with floor-function coefficients that are constant mod 2 never changes the cokernel. It fails:
  - at α = 1;
  - for coefficients per matrix entry (even when ≡ const mod 2, at α up to 8);
  - for floor functions that are not constant mod 2.
- **The law is not formal (MEASURED):**
  - on random lattices with only the symmetric functions it fails 3/813 (PA.0);
  - on random «Borel lattices» (divided powers of F and the floor, no E) it fails 24/632 (PB7.4).
- Flight 7 concluded «any proof must use the whole tilting structure». **Read §2 below: that conclusion is now too strong.**

## 2. Rafa's two images, and what the auditor measured before writing this mission

Read `material/bross_images/MEDIDA_IMAGENES_BROSS_v1.md` (the record) and `material/bross_images/SEALED_BROSS_IMAGES_v1.md` (sealed before measuring). The engine is `material/bross_images/gb8_images.py`; its logs are beside it.

### 2.1 Image 1 — the air conditioner that leaks inside the room
Rafa, verbatim: «Esto suena a cuando el aire acondicionado pierda agua por dentro, el aparato de dentro de la habitacion, se satura la bandeja, y caen siempre por el mismo sitio, debe estar taponado el desague de la condensacion. Si lo encuentras, ese es el mecanismo que taponado, hace que las gotas caigan siempre en el mismo sitio».

| image | mathematics |
|---|---|
| the tray | M = L/2L with x_i = F^(2^i) mod 2 (commuting, x_i² = 0). It is full and exact: ker x₀ = im x₀. |
| the condensation left in the tray | M̄ = M/x₀M |
| the drain | how x₁ (the doubling side, e₂ ≡ x₁) and ȳ = (a − 1) mod 2 (the folding side) act on M̄ |
| the clogged drain: the drops always fall in the same place | **(D0): rank_M̄ x₁ = rank_M̄ ȳ** |

What the auditor found:
- **Lemma D (PROVED, pencil, one hand).** For a lattice with ker x₀ = im x₀, free over Z₂[a], at every shift i ≥ 1: X̄ and 2X have the same NUMBER of cyclic factors ⟺ D0. D0 does not depend on the shift.
- **Lemma D-odd (PROVED, pencil, one hand).** Every odd family T(2l′+1) satisfies D0.
  - Proof: on Φ(N), M̄ ≅ N/2N.
  - There x₁ acts as x₀ of N, and ȳ acts as (a_N − 1) mod 2.
  - Both have rank dim N/2, because N is x₀-exact and Z₂[a]-free.
  - **The drain of T(2l′+1) is the tray of T(l′).** That is the plug.
- **MEASURED:** D0 holds on every T(l), l ≤ 30. On M̄, rank x₁ = rank ȳ = dim/4 for l ≥ 3.
- **MEASURED, the decisive one:** in flight 7's own Borel run (the auditor reproduced its tally exactly) and in a fresh run of the same generator:
  - **every one of the 52 failing cells is D0-false**: 13 lattices × 4 shifts, with the number of factors different;
  - **every one of the 305 kept lattices with D0 true obeys the law at every shift**;
  - **every (P) failure on a kept Borel lattice (9 + 15 = 24) is on a D0-false lattice; 1 220 of 1 220 (P) cells hold on D0-true lattices.**
- So flight 7's counterexamples all leak in the tray, not in the exponents. **Conjecture B″ (MEASURED, CONJECTURE):** for every Borel lattice L with ker x₀ = im x₀, free over Z₂[a] and satisfying D0, X̄(L, i) ≅ 2X(L, i) for every i ≥ 1, and (P) holds at α = 2.
- **Caution: two runs of one random generator.** The generator that refuted flight 7's Conjecture B was its «deep» one. B″ must face harsher generators before you build on it (Leg 0).

### 2.2 Image 2 — Dalí's clocks, found in the sand
Rafa, verbatim: «Los relojes en la playa son de Dalí (de su famoso cuadro La persistencia de la memoria), pero si los encuentras en la arena... son de quien los haya perdido».

| image | mathematics |
|---|---|
| melted clocks that still tell the time | Lemma P: the payment operator with weights ζ_mF^(m) hung on it has the same cokernel |
| Dalí's clocks: persistence as art, with no owner | a formal reason valid for every lattice; there is none (PA.0, PB7.4) |
| in the sand they belong to whoever lost them | each weight has an owner: ζ_mF^(m), hung m floors below, was dropped by the chain F^m = m!·F^(m) that it shortcuts |
| the owner pays | a term that jumps m floors uses m − 1 more diagonal entries, each paying the rent 2^α(f + c); margin (m − 1)α − v₂(m!) |

What the auditor measured (tilting lattices T(l), l ≤ 12 to 16 depending on the test, constant ζ, five trials per cell):
- At α = 1, weights only at the m that are not powers of 2: **never** move the hands (250/250).
- At α = 1, ζ₂ odd: moves the hands in 260/275 trials, alone or with any other weights (310/325). The number of factors never changes: the drain is clear, only the exponents move.
- At α = 1, ζ₂ even (with any other weights): never (325/325).
- **At α = 1, ζ₄ odd alone, or ζ₈ odd alone: never (225/225 each).** The auditor had predicted that ζ₄ would bite. It did not, and the failure is published in his record.
- At α = 2, any constant weights: never (275/275).
- **The owner law (MEASURED):** the only weight that can move the hands is the first one, ζ₂F^(2), and only when it is not paid: v₂(ζ₂) + α < 2.
- Weights per matrix entry move the hands even with the drain clear (flight 7's PL.e, PL.d). Weights that are not floor functions have no owner.

### 2.3 Two more images — the U-bar, and «force it to weigh differently»
Read `material/bross_images/MEDIDA_IMAGENES_BROSS_v2.md` (sealed first in `SEALED_BROSS_IMAGES_v2.md`; engine `gb8_UB.py`).

Rafa, verbatim:
- (A) «si es como doblar una barra y que haya las mismas piezas en cada lado, como si hicieras una U. Pon una pesa en cada lado y mide si detectan el mismo peso, como es estructural, debe serlo, ya mas medir no sirve, metele un infinito y pesas, ponle trucos y trampas, a ver si encuentras la ley.»
- (B) «obligale a pesar distinto, asi consegui enocntrar una ley estructural, obligando a frobenius a hacer arrugas en no se donde, y no podia, era estructural.»

**The U (flight 7's «one operator, two lattices»).** The two arms and the weight are:
- even families: arms T and hT inside T(ν) ⊗ Q, with h = (1 + τ + a)/2 and the weight f = 1 + τ − a. The law is T/f·hT ≅ T/f·T, because θ = f·h.
- odd families: arms C·N and E·N, C = Σ F^(s)/(4^s(2s−1)!!), E = Σ F^(s)/4^s, weight 4J.

What the auditor measured:
- **Even families, one bend reads the same; two bends do not.**
  - T/f·hT ≅ T/fT holds in 48/48 cells (the law).
  - With h², h³, h⁻¹ the reading CHANGES from ν = 7 on.
  - With 252 random weights g ∈ ½·Z₂[τ, a] that are odd on every eigenline (degree ≤ 2 in τ), it holds 252/252, and 215 of those g are not h times an integral unit.
  - **Candidate U-lemma (CONJECTURE): for every eigen-odd g ∈ ½·Z₂[τ, a], T(ν)/f·gT(ν) ≅ T(ν)/f·T(ν).** It has no specific owner: «one bend is free». With g = h it IS the even half of the fold law.
- **Odd families, the owner is exact.**
  - Replacing (2s − 1)!! by other odd units changes the reading in about two thirds of the trials. That holds even for units ≡ (2s − 1)!! mod 4.
  - So «the same series up to odd units» is not a principle. The odd half must go through the operator side, Lemma P, where constant weights never matter.
- **Force it (B): it cannot be forced at α = 2.**
  - On T(l), l ≤ 12, with weights ±(2^40 + 1), shifts c = 1024, 1025, and odd floor-dependent ζ₂, it holds 616/616.
  - The only place where the reading was ever forced is α = 1 with ζ₂ odd.
  - This is the «Frobenius could not wrinkle» signature. (O-first) and (O-high) at α ≥ 2 are the structural target.

### 2.4 The map, in one paragraph
Lemma P, and with it the fold law, has two layers.
- **The tray (mod 2):** the number of cyclic factors. It is governed by D0. D0 is proved for odd families, measured for even families, and is the only thing that fails in every known counterexample.
- **The owner (2-adic):** the exponents. On every lattice with a clear drain, nothing has ever moved them. On tilting lattices, the only weight that can move them is F^(2) at α = 1.

**Your job is to prove both layers for every tilting lattice.** For the even families the U-lemma (§2.3) is a candidate shortcut; for the odd families the owner lives on the operator side (Lemma P).

## 3. Your target

**Prove, for every family λ ≥ 1 and every shift i ≥ 1, that X̄(λ, i) ≅ 2·X(λ, i).** Then:
- with flight 6's Lemma Z0 (shift 0) and §4.2 (assembly) this gives, for every n:
  **Syl₂ K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄(n) with every exponent raised by one]**, a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}.
- Lemma Z0 rests on flight 6's normal forms. If you use it, re-derive it in your own words.
- Or prove shift 0 directly, as Lemma H already does at j = 0 for the odd families.

You do NOT have to prove (Q), (Q_even), PL\* or B″ in full. They are sufficient, not necessary. What is needed is an isomorphism of cokernels for the tilting lattices.

## 4. The plan

### Leg 0 — calibration, the two small pencils, and the stop rule for B″ (budget 15 %)
1. **Calibrate.** Copy `material/bross_images/gb8_images.py` and flight 7's `tilt_dp.py`, `borel_lat.py`, `m7lib.py` into `engines/`; fix the `sys.path` line. Reproduce three things:
   - `tilt 30` (D0 30/30);
   - `borel 400 5` (tally 158 kept, 24 failing; CROSS 24 noD0, 152 D0 all pass);
   - `owner 12 5` (SO1–SO6 as in the log).
2. **Pencil: D0 for even families.** λ = ν + 1, T(λ) = V ⊗ T(ν). Prove D0, or find the even family where it fails (then that is a counterexample to the law: the Stop rule below).
   - Use flight 7's A2.2: (V ⊗ M)^a ≅ M.
   - Or work on the (n − 1)-cube form directly: f = 1 + τ − a against θ = τ(τ + 2)/2 on T(ν).
3. **Pencil: the even families as payment operators.** Check whether one more P-R1 compression of the H-even operators on T(ν) = Φ(T(λ₁)) turns both coker(1 + τ − a) and coker(τ(τ + 2)/2) into payment operators on T(λ₁) at the same α, differing only by weights in the safe class.
   - If yes, write it.
   - If not, write exactly what the even case needs instead. Flight 6 §3.6 has a gluing form: «σ_A ⊕ σ_C on N ⊕ N glued by ω̄, against glued by the identity».
   - **Or prove the U-lemma (§2.3)** for every eigen-odd g ∈ ½·Z₂[τ, a] on T(ν), ν odd. It is measured, has no owner, and gives the even families at once. Gate it. Controls that must fail: g = h², h⁻¹ (from ν = 7), and g with an even eigenvalue.
   - Say why one bend is free and two are not. The measurement says the difference is the depth of the denominator, ½ against ¼.
4. **Stop rule for B″ (sealed first).** Run harsher Borel generators:
   - strings up to length 16;
   - offsets 0..6;
   - up to six generators, with denominators up to 16;
   - at least two seeds.

   If a kept lattice with D0 true breaks the fold law or (P), B″ is false. Write it on the first line of the report, and go to Route B of Leg A. If B″ survives, say how hard you pushed it.

### Leg A — the owner layer, for tilting lattices (budget 50 %)
Choose a route, write why, and prove the family law. Gate every lemma against `tilt_dp.py`, with controls that can fail (α = 1 with ζ₂ odd; weights per matrix entry; the D0-false Borel lattices).

**Route D — «each drain feeds the next tray» (recommended first).**
- Lemma D-odd works because, on Φ(N), the mod-2 layer of the fold law is the Z₂[a]-freeness and x₀-exactness of N: one floor down, one level down.
- Look for the same recursion at every 2-adic level k. Let c_k(A) = number of Smith exponents of coker A that are ≥ k. The family law is c_k(folded) = c_k(doubled) for every k.
- Find, for each k, the rank statement D_k on an explicit subquotient whose truth is c_k-equality. Then prove: on Φ(N), D_k for the family 2l′ + 1 follows from D_{k−1} (or from the payment rule) for N.
- Flight 2's P-R1 already does «one doblar = halve the lattice, double the payment». The question is whether it carries the two sides of the fold law, level by level, into each other.
- The even step (V ⊗ Φ) is where flight 7 stopped. Do it with Leg 0's item 3.

**Route A′ — the owner's margin in the final matrices.**
- The closed rule computes coker(F + 2^α(D + c)) by flight 2's dance down to final matrices M(λ, c, α) of size 2^|I|.
- Their Smith form is fixed by valuations alone:
  - Theorem O (flight 3) gives one minor with a unique cheapest term;
  - Theorem F (flight 4) gives the cost bound on every matching.
- Run the dance on the perturbed operator. Show **valuation dominance**: every perturbed entry exceeds the entry's tropical weight. Then O and F transfer word for word.
- **The owner law tells you where to look:** only the weight F^(2) can ever tie. Prove first:
  - **(O-high)** the weights m ≥ 3 never move the hands, at any α ≥ 1;
  - **(O-first)** the single weight ζ₂F^(2) never moves them when 2^{2−α} | ζ₂.
- The two together give Lemma P at α ≥ 2, hence the odd families. Measure first, on the final matrices, whether dominance holds entry by entry (λ ≤ 20, α = 2, 3, c ≤ 6); controls: α = 1 with ζ₂ odd must violate it.

**Route B — the Δ/∇ mirror (only if B″ falls in Leg 0, or Routes D and A′ stall).**
- The law holds on Weyl and dual-Weyl lattices (flight 7 PN.1–PN.2; flight 6 Theorem W̄).
- T(l) has both filtrations. Induct along a Δ-filtration. The obstruction to lifting an isomorphism of cokernels lies in an Ext¹ between two Z₂[x]-modules (x acting by the folded operator on one, by the payment on the other).
- Kill it with the ∇-filtration: Ext¹(Δ, ∇) = 0 is the standard tilting fact (Jantzen, II.4.13). It is not in this folder in the original; cite it as standard and say so.
- First write the exact Ext¹ group, and check that it is NOT zero for the D0-false Borel lattices.

**Ten-minute rule:** ten minutes without traction on a route — write what you have, mark it, take the next route.

### Leg B — assembly (budget 15 %)
- From the family law, the fold law for every n, with every dependency named (flight 7 §3.1 is the template).
- Gate: your engine against the cells n ≤ 60 (928 cells; flight 7's `fold_cells.py` does it in 42 s).

### Leg C — what is left (budget 20 %, the last fifth is for writing)
- If the general proof closes, write it whole, once more, in clean form. The auditor will read it line by line.
- If it does not close, write the strongest statement you PROVED, and the exact statement still missing. Write it as one lemma with every hypothesis named.

**Stop rule (counterexample to the law):** a family λ and a shift i with X̄(λ, i) ≇ 2X(λ, i). It goes on the first line of the report, with the smallest n where it appears. None is known for n ≤ 100.

## 5. What the auditor will accept as «closed»
- A pencil proof of the family law for every tilting lattice T(λ), λ ≥ 1, every shift i ≥ 1, plus shift 0, with every step gated on λ ≤ 20.
- Controls that can fail, and do fail where the law or the lemma is false: α = 1 with ζ₂ odd; weights per matrix entry; the D0-false Borel lattices; T(0).
- It will be read twice: by you, then by the auditor with his own code.

## 6. The house vocabulary (Rafa's images; say which served and how)
- **The air conditioner whose drain is clogged** (this mission): the tray is full, the drops always fall in the same place. Find the plug: the mechanism that makes them fall there.
- **Dalí's clocks in the sand** (this mission): melted clocks that still tell the time are Dalí's. In the sand they belong to whoever lost them. Find each weight's owner.
- **The U-bar** (this mission): bend a bar into a U, with the same pieces on each arm, and hang a weight on each: they must read the same. Measured: one bend reads the same, two do not.
- **Force it to weigh differently** (this mission): Rafa found a structural law in the Chaise Longue by forcing Frobenius to wrinkle where it could not. Here the law cannot be forced at α ≥ 2.
- **The leaks** (the auditor's image after flight 7): fold the house or double it, and the leaks fall in the same places; the reason is in the whole roof.
- **The clock with weights:** the folded clock is the doubled clock with weights hung on it, and it shows the same time (Lemma P).
- **The mirror that doubles; «se van turnando»; the plumber; the orphan; the rent and the gold dust** — earlier flights (see `material/`).

## 7. Budget
- Write the estimate before each leg and each run.
- Keep the last fifth of your time for writing.

## 8. Sections of REPORT.md (create them empty first)
0. First line — does this flight prove the fold law for every n, yes or no
1. Leg 0 — calibration, D0 for even families, the even families as payment operators, the stop rule for B″
2. Leg A — the owner layer
3. Leg B — assembly
4. Leg C — what is left
5. Images — which served
6. Sealed predictions, hits and failures
7. My errors
8. The story of this flight, in plain words
9. Files with md5
