# MISSION 9 (version 2) — «Grepy el volador 9»: THE OIL, THE CAVE AND THE PAIR OF HINGES — Lemma Ω, the last lemma of the Dry and Wet Law

Written by Grepy Bross, the auditor of the hypercube project, on 4 October 2026 (night). You are a NEW constructor: Rafa orders a fresh Claude for each mission. You never met the eight pilots before you. Everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §8, empty.
2. Every lemma goes into `REPORT.md` the moment you have it, before you look for the next one.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Write each leg's estimate in `REPORT.md` BEFORE you start the leg, and each run's estimate (memory and time) BEFORE the run.
5. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each leg. If your window is compacted, re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, then go on from the last leg that is not CLOSED.
6. What is not on disk does not exist. A write that fails must not be reported as done: check the file, then write the diary line.
7. Tell in `REPORT.md` §8, in plain words, how each idea came: Rafa wants the story.

**Where you work**
- Write only inside `~/Desktop/GREPY_EL_VOLADOR_9/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`. Never use `rm`. Never read a Desktop screenshot.
- `material/` is read-only. Copy any engine you run into `engines/` and fix its paths there (the auditor's engines import flight 8's `fdance.py` from `VOLADORES/GREPY_EL_VOLADOR_8/engines`; here it is `material/flight8/engines`).

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. One heavy job at a time. Integers and exact fractions only.
- A log that does not end in `VIGIA-FIN-OK` is not a result.

**Grades:** **PROVED** (pencil, with a gate), **MEASURED**, **READING**, **CONJECTURE**.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds. Publish failures in the same size of type as hits.
- A control must be able to fail; say which of yours did.
- Do not mark PROVED what you have only sketched.

Chat with Rafa in Spanish; documents in English.

## 1. Where the cube stands

**Closed.** The Dancing Sand Theorem — the whole Syl₂ K(Q_n) for every n by a closed rule (flights 1–4; two readings). Read `material/AUDIT_FLIGHT_4.md` if you need the rule; you do not need it to work.

**The second theorem, «The Dry and Wet Law» (the fold law):** 2K(Q_n) ≅ K̄(n) on 2-parts, K̄(n) the sandpile group of the folded cube.
- It follows from the **family law X̄(λ, i) ≅ 2X(λ, i)** for every tilting lattice T(λ) and shift (flights 6–8; `material/flight8/REPORT.md` §3.1, §4.2).
- **PROVED for every n ≤ 144** (flight 8's Theorem C₈). Its **mod-2 layer is PROVED for every n** (Lemma D-even, two readings).
- **For every n it is reduced to ONE lemma, Lemma Ω («the owner pays»).** Read `material/flight8/REPORT.md` §2.2–§2.10 and §4.2–§4.4 and `material/AUDIT_FLIGHT_8.md` FIRST. Everything below uses their notation: the formal Borel algebra 𝔅 (elements Σ_m φ_m(D)F^(m), product (φF^(a))(ψF^(b)) = C(a+b, a)·φ(D)ψ(D − a)F^(a+b)), flight 2's dance with its two moves (doblar = Φ, paso = V⊗Φ), clean moves, the word w(l).
- **Rafa's decision: the law WILL be closed for every n. There is no fallback to a conjecture.** Your job is to close Ω. If you do not, you report exactly how far you got; you do not propose to print it as a conjecture.

**Lemma Ω, as flight 8 left it (§4.2 of its report).**
- **Ω-odd (= (R_gen)).** Over R = Z₂⟨q_d, ζ_m⟩, Σ = F + 4q(D), A = Σ + Σ_{m≥2} ζ_m F^(m): along every word every move of the dance of A is clean, and M_w(A) − M_w(Σ) ∈ 2·M_w(Σ)·R entry by entry.
- **Ω-even.** The two final matrices of an even family (Lemmas E2/E4 systems circ(f), circ(fh)) are associates: M(circ(fh)) ∈ M(circ(f))·GL(Z₂).
- Where it sticks: the coupling's F-terms are large (valuation = coupling − 1) and cancel EXACTLY one doblar later (3 + 3 → 8). Nobody has the closed form of the perturbed glue t. A floor glue does not fit (§2.9 item 5); the Sylvester glue has denominators down to 2⁻¹³ (§4.4).

## 2. Rafa's two images, and what the auditor measured tonight

**Rafa's words.**
1. «¿Qué forma tiene una bisagra cuyo ruido de hoy se borra mañana? La misma: se le echa aceite engrasante hoy y ya no hay ruido. Es la misma, sin ruido, y brilla más el metal.»
2. «Cuanto más bajas, haz todo a la mitad, que el agujero se va estrechando. Es la única forma de bajar, como arrastrarse por una cueva donde el hueco es más pequeño cada vez, como en Cadena perpetua cuando se escapa el protagonista. Tiene que servir y cerrar la ley.»

**The auditor's translation** (sealed before measuring: `material/auditor_oil/TRANSLATION_AND_SEALS_v1.md`).
- **The hinge** = the coupling K of the 2-dancer system G = [[X, 0], [K, Y]] that a paso produces (the two arms X, Y of the U).
- **The same shape** = the unperturbed glue. When the word starts with a paso, the unperturbed coupling is EXACTLY K₀ = t₀(Y₀ − X₀) with the scalar t₀ = 2^(−α) (gate: 135/135 cells; with a doblar before the paso the unperturbed glue is no longer a scalar, so use the Sylvester solution of the unperturbed system).
- **The oil** = integral row and column operations: K ↦ K + P·X + Y·Q with P, Q ∈ 𝔅 over Z₂. They are invertible lower-triangular operations, the dance moves are algebra maps, so **oil never changes the cokernel on any lattice, nor the cleanness of any move**.
- **«It is the same, without noise»** = **(H1)**: R := (Y·t₀ − t₀·X) − K ∈ 𝔅_{Z₂}·X + Y·𝔅_{Z₂} (t₀ = the UNPERTURBED glue, X, Y, K the PERTURBED system). Then the perturbed system is oiled into L_{t₀}⁻¹·diag(X, Y)·L_{t₀}: the same hinge, and the whole perturbation lives in the arms, which are single-dancer systems (where flight 8 §2.9 item 1 already works).
- **The staircase halved, the cave** = track the noise RELATIVE to the scale of each level, and ask that it never grow.

**What was measured** (engine `material/auditor_oil/gh_bisagra_aceite.py`, logs beside it; all VIGIA-FIN-OK, ≤ 15 MB). Oil test = exact membership of R in the Z_(2)-span of the columns of the linear map (P, Q) ↦ PX + YQ, truncated to the floors of the level (complete for the dance, which is causal in floors).
| test | result |
|---|---|
| S1: H1 at the first paso, α = 2, 3, c = 1..3, l ≤ 24, ζ₂..ζ₅ ∈ [−5, 5] | **FAILED as sealed: 100/216** |
| weight by weight: ζ₃ alone, ζ₄ alone, ζ₅ alone | **the oil exists in 216/216 for each** |
| ζ₂ alone | fails only when ζ₂ is ODD (113 failures, all with ζ₂ odd; 12 odd cells still oil; ζ₂ even: 91/91 oil) |
| all weights together, ζ₂ even | 3 cells fail although each weight alone oils: an interaction, small but real |
| S2 control: α = 1, ζ₂ odd | 6/108 oil — the control fires |
| S3 control: the wrong glue 2t₀ at α = 2 | 0/108 — the test discriminates |
| H1′: the same test one or more levels later (Sylvester unperturbed glue), l ≤ 22 | level 0: 75/216; level 1: 70/96; level 2: 31/36; level 3: 12/12 |
| the cave: defect e_h = least e with 2^e·R oilable, level by level, ζ₂ odd, l ≤ 30 | **312 cells; every integer sequence is NON-INCREASING** (18 start with «> 20»); 90 reach 0 before the next paso |
| S4: does each paso add α − 1 to the relative valuation of the final matrix? | **FAILED as sealed (257/342): the toll is FLAT — min(ν(M′ − M) − ν(M)) is exactly α − 1 for 0, 1, 2, 3 pasos** |

**And why ζ₂ odd is not a corner case** (auditor's pencil): for the odd families the weights are those of u·tanh(u/2) with u² = 2F, and u·tanh(u/2) = u²/2 − u⁴/24 + … = F − F^(2)/3 + …: **ζ₂ = −1/3, a 2-adic unit.** The real case is the hard case.

**Reading of the measurements.** The oil removes every weight except the square one, ζ₂F^(2). The squeak that ζ₂ leaves is real (Shawshank: you crawl through the dirt), but it never grows from one level to the next, and it often vanishes before the next paso. The toll on the final matrix does not accumulate; it is exactly one payment, α − 1, at every depth: the hole keeps its width, and α − 1 ≥ 1 is precisely «you still fit through» (at α = 1 the dance jams, the control).


## 2 bis. Rafa's third image: hinges come in pairs — and the random weights were the bug

**Rafa's words.** «Las bisagras suelen ir siempre en pareja; rara puerta o ventana tiene una bisagra. Mide a ver si van a ser 108 bisagras cada una bien engrasadas, o 216 entre más bisagras. Los bugs son hallazgos casi siempre.»

**Translation.** The table of §2 used RANDOM weights ζ_m. The fold law never needs random weights: by Lemma H-odd (flight 7) the odd families carry the REAL weights of two series, and they come in pairs with the same c (the same payment 4(D + c) up to an odd unit):
- shift j = 2c, ε = +1: A_tanh = 2(2D + j) + (Ch − 1)Sh⁻¹ (= u·tanh(u/2); weights 1, −1/3, 1/5, −17/105, 31/189, …);
- shift j = 2c − 1, ε = −1: A_coth = 3·(2(2D + j) + (Ch + 1)Sh⁻¹) (= 3u·coth(u/2); weights after ×3: 1, −1/15, 1/105, −1/525, 1/2079, …).
The two hinges of one door = these two odd arms (the even family between them is their U, Lemma E3).

**What the auditor measured** (`material/auditor_oil/gh_bisagras_pareja.py`, `gh_bisagras_pareja_24.py`, logs `pareja_16.log`, `pareja_24.log`; oil defect e = least e with 2^e·R oilable, level by level from the first paso; words starting with a paso, l even ≤ 24, c ≤ 5: 60 doors, 120 hinges).
| test | result |
|---|---|
| a single real hinge oils at once (sealed P1, P2) | FAILED: it squeaks |
| **how much it squeaks** | **at most ONE factor 2 in every cell (max defect 1); with random weights the defect went above 20** |
| **the two hinges of the same door (same c) squeak identically, level by level (sealed P3)** | **HELD, 60/60** |
| control: the other adjacent pair (shift 2c with 2c + 1, different c) | identical only 28/60 |
| the squeak of 1 disappears further down | in 27/60 doors (the other 33 have no further level before the next paso) |
Pencil remark: A_coth/3 at j = 2c − 1 equals A_tanh at j = 2c plus 2(Sh⁻¹ − 1), and Sh⁻¹ − 1 = −F/3 + …: the two hinges differ by 2 × (an element of 𝔅).

**What this changes in your job.** Flight 8's Ω-odd asks for EVERY constant weight (R_gen). For the fold law you only need the two real series. **Your first target is Ω-real:** Lemma Ω for A_tanh and A_coth at every shift, along every word. With the real weights the oil route has a defect of at most 1 to absorb, and the toll at α = 2 is exactly 1 (§2, S4): one factor 2 against one factor 2. Prove that this is not a coincidence.

## 3. Your job

**Close Lemma Ω for every word — first Ω-real (§2 bis), then, if it costs little more, flight 8's general Ω.** The route proposed by the images is the OIL ROUTE below, run on the REAL weights. You may take another route if you find a better one; say why.

### Leg 0 — calibration (budget 10 %)
- Copy the auditor's engines into `engines/`, fix the import path, and reproduce: the gate (t₀ scalar when the word starts with a paso), S1–S3, the weight-by-weight table, H1′ and the cave. **Write your own independent oil test** (different linear algebra, e.g. a 2-adic Smith form of the column matrix) and gate it against the auditor's on the same cells.
- Reproduce also §2 bis (the pair table, and the control pair).
- Seal before measuring.

### Leg A — the oil exists for every weight but the square (budget 25 %)
- **(A0) The pair identity (new, do it first).** Prove that the two hinges of a door are the same hinge: the identical defect sequences of A_tanh (j = 2c) and A_coth (j = 2c − 1). Start from A_coth/3 = A_tanh + 2(Sh⁻¹ − 1) and the fact that oil does not see a change of 2 × (something) when the defect is at most 1. Then prove **the real squeak is at most one factor 2** at the first paso, for every word and every c.

Then prove by pencil, for every word that starts with a paso and every α ≥ 2, c ≥ 1:
- **(A1)** If ζ₂ = 0 (weights ζ_m, m ≥ 3, arbitrary in R), then H1 holds, with an EXPLICIT oil (P, Q) in closed form. Find it numerically first (solve for P, Q and look at their coefficients), then prove it.
- **(A2)** For general ζ, write R = R₂ + R_rest with R_rest oilable by (A1)'s formulas, and R₂ the ζ₂-squeak in closed form (flight 8's Sylvester data: with ζ₂ alone, t = ¼ − ζ₂(D + 1) − (ζ₂²/8)F; the integral part −ζ₂(D + 1) is oilable for free; the obstruction is the F-term −(ζ₂²/8)F).
- Gate every formula on l ≤ 24, α = 2, 3, c ≤ 4.

### Leg B — the squeak is gone tomorrow (budget 30 %): the heart
- **(B1) The squeak's class.** The obstruction lives in the quotient 𝔈 := 𝔅/(𝔅X + Y𝔅) (integral). Describe it: what is the class of R₂ there, what is its order (the defect e₀)?
- **(B2) Transport.** Write how a doblar and a paso act on the triple (X, Y, [R]) — the moves are algebra maps, so they induce maps on 𝔈. Prove the measured fact: **the defect never increases** (e_{h+1} ≤ e_h), and find exactly when it drops.
- **(B3) The bottom.** For the real weights the squeak is at most 1 and the toll is exactly 1: show the squeak is absorbed by the toll. At the bottom of the dance only constant terms at floor 0 survive. Prove that there the squeak is absorbed: either its class is 0, or it is a multiple of the toll (α − 1 ≥ 1 extra factors 2) and so cannot move the Smith form. **This is the precise form of «Rafa: la misma, sin ruido».** With it: the perturbed final 2-dancer system is integrally equivalent to the glued form L_{t₀}⁻¹·diag(X, Y)·L_{t₀} with perturbed arms, and single-arm statements finish (flight 8 §2.9 item 1, constant terms keep their exact valuation).
- **(B4) Many dancers.** After a second paso the system has 4 dancers (then 8, …). The unperturbed shape is a nest of glues. Extend the oil test, the defect and (B2)–(B3) to the nest. Measure first (seal), then prove.
- **«Brilla más el metal» — the alternative if (B3) fails.** Allow the oil to change the arms as well (X ↦ U·X·U′ with U, U′ units of 𝔅): the equivalence class of the whole system, not only of the coupling. Try first the gauges that remove ζ₂ from the arms' F-coefficients.

**Ten-minute rule:** ten minutes without traction on a route — write what you have, mark it, take the next route.

### Leg C — Ω-even (budget 10 %)
- The even families are two odd arms glued by ½ (flight 8 Lemma E3, E4). Show that the oil route gives Ω-even (association) once Leg B gives Ω-odd, or say exactly what extra is needed.

### Leg D — assembly and what is left (budget 25 %, the last fifth is for writing)
- If Ω closes: write the fold law for every n, every dependency named (flight 8 §4.2 «What Ω gives» is the template), and the proof of Ω whole, once more, in clean form. The auditor will read it line by line.
- If it does not close: the strongest statement you PROVED and the exact statement still missing, as ONE lemma with every hypothesis named.

**Stop rules.**
- **Counterexample to the law:** a family λ and shift i with X̄(λ, i) ≇ 2X(λ, i). First line of the report. None is known for n ≤ 144.
- **The oil route dies** if, for some word, the defect at the bottom is positive AND the final Smith forms differ, or if (B2) is false (a defect that grows). Then say it on the first line and switch to «brilla más el metal».

## 4. What the auditor will accept as «closed»
- A pencil proof of Lemma Ω (odd and even) for EVERY word, with every step gated on l ≤ 24 (and l ≤ 12 symbolically over R).
- Controls that can fail and do fail where they must: α = 1 with ζ₂ odd; the wrong glue 2t₀; ζ₂ odd without the second level.
- It will be read twice: by you, then by the auditor with his own code.

## 5. The house vocabulary (Rafa's images; say which served and how)
- **The oiled hinge** (this mission): the same hinge; the noise of today is gone tomorrow; the metal shines more.
- **The cave / Shawshank** (this mission): halve everything as you go down; the hole narrows; it is the only way down; you crawl through the dirt and come out clean.
- **The staircase and the toll** (flight 8): each step folds and keeps half; each weight pays a toll and cannot save more than one factor 2.
- **The AC drain, Dalí's clocks, the U-bar, force it** (flight 8; `material/flight8/MISSION.md` §6).

## 6. Budget
- Write the estimate before each leg and each run. Keep the last fifth of your time for writing.

## 7. Files in `material/`
- `flight8/` — flight 8's REPORT, MISSION, engines (fdance.py is the formal dance), checks, logs.
- `AUDIT_FLIGHT_8.md` — the auditor's audit of flight 8.
- `auditor_oil/` — tonight's translation, seals, engines and logs (this section's table).
- Everything else — flights 1–7 and their audits (as given to flight 8).

## 8. Sections of REPORT.md (create them empty first)
0. First line — does this flight prove Lemma Ω (and so the fold law for every n), yes or no
1. Leg 0 — calibration
2. Leg A — the oil exists for every weight but the square
3. Leg B — the squeak is gone tomorrow
4. Leg C — Ω-even
5. Leg D — assembly and what is left
6. Images — which served
7. Sealed predictions, hits and failures
8. The story of this flight, in plain words
9. My errors
10. Files with md5
