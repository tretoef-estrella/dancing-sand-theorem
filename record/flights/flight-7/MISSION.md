# MISSION 7 — «Grepy el volador 7»: THE FOLD LAW FOR EVERY n

Written by Grepy Hypercube, the auditor of the hypercube project, on 4 October 2026. You are a NEW constructor (Rafa's order: a fresh Claude for each mission). You never met the six pilots before you. Everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §7, empty.
2. Every lemma goes into `REPORT.md` the moment you have it, before you look for the next one.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Write each leg's estimate in `REPORT.md` BEFORE you start the leg, and each run's estimate BEFORE the run. Flight 6 had pencil in its head for minutes before its estimate was on disk (its E1, E2): do not repeat it.
5. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted, re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, then go on from the last leg that is not CLOSED.
6. What is not on disk does not exist. Tell in `REPORT.md` §8, in plain words, how each idea came: Rafa wants the story.

**Where you work**
- Write only inside `~/Desktop/GREPY_EL_VOLADOR_7/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`. Never use `rm`.

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time.
- Integers and exact fractions only. Flight 6 lost a run to a float leak (its E7).

**Grades:** **PROVED** (pencil, with a gate), **MEASURED**, **READING**, **CONJECTURE**.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it.
- Publish failures in the same size of type.
- A control must be able to fail.

Chat with Rafa in Spanish; documents in English.

## 1. Where the cube stands (read `material/flight6/FLIGHT6_REPORT.md` and `material/AUDIT_FLIGHT_6.md` first)

The whole 2-part of the sandpile group `K(Q_n)` is known for every n by a closed rule. This is flights 1–4 (audited; `material/AUDIT_FLIGHT_4.md`):

  **Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ X(λ, (n−λ)/2)^{m_λ(n)}**,

a sum over the tilting families of V^{⊗n} (SL₂, characteristic 2).

**Flight 6 (audited 4 Oct)** proved Gao et al.'s Conjecture 5.4 for every k. On the fold law it proved:
- **Lemma RT̄:** the folded cube splits along the same families: **Syl₂ K̄(n) ⊕ Z₂ ≅ ⊕_λ X̄(λ, i)^{m_λ(n)}**, with X̄(λ, i) = T(λ)/(τ_i T + (a − 1)T), τ_i = F + 2(D + i) and a = (−1)^{D+i}·exp F. Here exp F = Σ_m F^{(m)}, and D is the floor.
- **The fold law follows from the family law X̄(λ, i) ≅ 2·X(λ, i)** (§4.2).
- **The family law for every Steinberg family**, by pencil: the fold keeps the even eigenvalues, and the symmetric functions on even c are the doubled payment (Lemma Π, Theorem W̄).
- **Two reductions:**
  - **odd families** λ = 2l₁ + 1 ⟸ **(Q)**: (T(λ)^a, τ_j) ≅ (T(l₁), F + 4(D + ⌈j/2⌉)) as Z₂[x]-modules;
  - **even families** λ = 2l₁ + 2 ⟸ **(Q_even)**: (T(λ)^a, τ_i) ≅ (T(l₁) ⊕ T(l₁), Lemma N's normal forms Ξ′, Ξ″).
- **46 exact certificates** (explicit integral intertwiners with odd determinant) for l₁ ≤ 13 and l₁ ≤ 9: the fold law for n ≤ 21 and n = 23, 25, 27.

**The auditor's second route** (`material/auditor_flight6/`) computed X̄ and 2X cell by cell, at the shift each n needs, on flight 6's lattices. **The fold law holds for every n ≤ 60.** No failure anywhere.

**What is NOT known: the fold law for every n.**
- Flight 6 showed (§3.8) that no natural isomorphism exists: no formula in F alone can conjugate.
- (PB.7) The obvious intertwiner e^{−F/4}·diag((2f−1)!!)·e^{κ} is integral only on the Steinberg lattices.

## 2. Your target — THE FOLD LAW FOR EVERY n

**Prove, for every family λ and every shift i ≥ 1, that X̄(λ, i) ≅ 2·X(λ, i).** With flight 6's Lemma RT̄, its Lemma Z0 (shift 0) and §4.2, this gives:

  **Syl₂ K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄(n) with every exponent raised by one]**, for every n.

You do NOT have to prove (Q) or (Q_even). They are sufficient, not necessary. **The statement needed is an isomorphism of cokernels**, which is weaker than a conjugacy. Choose the route.

## 3. Three routes (READING, for you to test, not to trust)

**Route 1 — the doubled payment, recursively (recommended first).**
- Flight 6, Lemma Π: X̄(T) = X^{(2)}(π_e T), the cokernel of the α = 2 payment on the even half π_e(T).
- Flight 2 (`material/FLIGHT2_REPORT.md` A.1, A.2, B.1, C.0) computes X^{(α)} for the lattices T(λ) by a recursion on (payments, couplings) along the two moves T(2l+1) = Φ(T(l)) and T(2l+2) = V ⊗ Φ(T(l)).
- **Question:** does π_e commute with the two moves, up to that same recursion? Concretely:
  - is π_e(Φ(N)) built from N by a move whose effect on X^{(2)} is the same as the identity's;
  - is π_e(V ⊗ Φ(N)) related to π_e(Φ(N)) by the step of flight 2's B.1 at α = 2?
- If the recursion of flight 2 reaches only through cokernel data (payments and couplings up to units), conjugacy is never needed.
- Test every candidate step against `material/flight6/engines/tilt_dp.py` and the auditor's `gh_audit_vuelo6.py` mode N.

**Route 2 — the whole ring.**
- Flight 6 §3.4(e): in C = R/σR, with C[2] = e₂C (fold-law note §1.1), the fold law is **C/e₂C ≅ C/(Σ_{k even ≥ 2} u_k e_k)C** with units u_k = (3k+1)/(k+1).
- Mod 2 the right side is Π_{t≥1}(1 + e_{2^t}) − 1.
- Is there a ring automorphism of C ⊗ Z₂ (or an isomorphism of C-modules) sending e₂ to an associate of Σ u_k e_k? Flight 6 never tried this route.

**Route 3 — (Q) and (Q_even) by induction.**
- (Q) holds for Weyl modules (cyclic lattices) and was certified for l₁ ≤ 13.
- T(l₁) has a Weyl filtration. An induction on the filtration, or on the two moves, that builds the intertwiner module by module would prove (Q). The descent obstruction (§3.8) only says it is not a formula in F.

**Stop rule (counterexample):** a family and shift where X̄ ≇ 2X is a counterexample to the fold law. It goes on the first line of the report, with the smallest n. The auditor found none for n ≤ 60.

## 4. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — calibration (budget 10 %).**
- Reproduce, with your own code, the cell law X̄(λ, i) = 2X(λ, i) for λ ≤ 12 and i ≤ 4.
- Use the lattices of `material/flight6/engines/tilt_dp.py` and your own Smith form.
- Copy any engine you run into `engines/` and fix its paths: `gh_audit_vuelo6.py` expects `engines_gh/`.

**Leg A — the route (budget 60 %).** Choose a route of §3, write why, and prove the family law for every λ and every i ≥ 1.
- If one route stops, say where and try the next.
- Gate every lemma against the lattices, with controls that can fail.

**Leg B — assembly (budget 15 %).**
- From the family law, the fold law for every n, and the rule for Syl₂ K̄(n) for every n.
- Name every dependency.
- Gate against the auditor's n ≤ 60.

**Leg C — what remains (budget 15 %).** If the general proof does not close, the largest n you can prove, and the exact statement left open.

## 5. The house vocabulary (Rafa's images; say which served)

- **The mirror that doubles:** folding the cube is the same as doubling it, except for a layer of Z/2's. It served flight 6 twice: the digit 0 of Conjecture 5.4, and the even eigenvalues.
- **«Se van turnando»:** each corner is the dry one for exactly one sink, its opposite. This image found the fold law.
- **«Binario, o está o no está, en secado o en mojado, y en el doble de horas»:** halving and doubling of the clocks.
- **The wound:** the sink heals by rotating.

For this flight, think of **the mirror built piece by piece**:
- the reflection exists for every piece of the cube, but there is no single formula for it;
- so build it the way the cube is built, one move at a time.

## 6. Budget

- Write the estimate before each leg.
- If ten minutes pass without traction, stop, write what you have, and mark the leg AGOTADO.
- Keep the last fifth of your time for writing.

## 7. Sections of REPORT.md (create them empty first)

0. First line — does this flight prove the fold law for every n, yes or no
1. Leg 0 — calibration
2. Leg A — the route
3. Leg B — assembly
4. Leg C — what remains
5. Images — which served
6. Sealed predictions, hits and failures
7. My errors
8. The story of this flight, in plain words
9. Files with md5
