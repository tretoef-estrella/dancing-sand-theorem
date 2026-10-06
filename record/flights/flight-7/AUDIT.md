# Audit — Flight 7 («Grepy el volador 7»: the fold law for every n), Grepy Hypercube, 4 Oct 2026

Delivery read cold: `~/Desktop/GREPY_EL_VOLADOR_7/REPORT.md` (237 lines, md5 `00ba2494d9137912a471c009335ab122`), `checks/SEALED.md`, `logs/DIARY.md`, and the eleven engines and thirty logs. After this audit the folder is MOVED into `VOLADORES/GREPY_EL_VOLADOR_7/` (manifest `reports/VOLADOR_7/ENTREGA_VUELO_7/MANIFEST_md5.txt`).

## 1. Verdict in one line

**THE FOLD LAW («The Dry and Wet Law») IS NOW PROVED FOR EVERY n ≤ 100, BY TWO INDEPENDENT COMPUTATIONS; FOR EVERY n IT IS STILL OPEN.**
- The flight did not find a general proof, and says so in its first line.
- It moved the proved range from n ≤ 60 to n ≤ 100. The auditor re-did that range with his own code (§4).
- Its most useful results are negative and mark the road: the law is **not** a formal consequence of the symmetric functions (PA.0) nor of the Borel structure, i.e. the divided powers of F and the floor (PB7.4). **A proof must use the whole tilting structure.**
- The kill criterion never fired: no counterexample in 2 548 cells.

## 2. Grades

| result | grade |
|---|---|
| Leg 0: cell law X̄ = 2X, λ ≤ 12, i ≤ 4 | MEASURED (flight), re-gated by the auditor in 140 cells (§4, G) |
| Lemma A0: X(λ,i)[2] = e₂X, so 2X ≅ T/(τ, e₂)T (λ ≥ 1) | **PROVED** (pencil; re-derived below) |
| Lemmas H-odd, H-even: X̄ as the cokernel of a half-size operator, every shift including 0 | **PROVED** (pencil; re-derived below; gated by the auditor's own implementation, 140/140 against the direct computation) |
| A2.1, A2.2: each family is «one diagonal operator on two lattices that differ by odd units» | PROVED (flight); A2.2 is gated through H-even; A2.1 not used by any conclusion |
| Lemma C (compressed form) | PROVED (flight); not re-derived; not used by any conclusion |
| A2.4: Steinberg families by determinants | SKETCH (the flight downgraded it itself, E4). Flight 6's Theorem W̄ stays the proof. |
| PL* (the safe class of perturbations) | MEASURED, 3 600 trials; CONJECTURE |
| PA.0, PB7.4: the law is not formal | MEASURED; the first Borel counterexample re-checked by the auditor with his own Smith form |
| Leg B, assembly «family law ⟹ fold law for n» | PROVED (flight 6 §4.2, restated with every dependency) |
| **Theorem C₇: the fold law for every n ≤ 100** | **PROVED**: pencil assembly + exact finite computation, done twice by independent codes (flight: `fold_cells.py`; auditor: `gh_audit_vuelo7.py`, §4) |
| The fold law for every n | **OPEN** |

## 3. Pencil reading (my own words)

- **Lemma A0 — CORRECT.**
  - τ = F + 2J with J = D + i, and e₂ := τ(τ − 2)/2 = F^(2) + 2FJ + 2J(J − 1) is integral (using JF = F(J + 1)).
  - For λ ≥ 1, T/2T is free over F₂[F]/(F²) (V is free and the algebra is Hopf), so ker F̄ = im F̄.
  - If 2x = τr: then F̄r̄ = 0, so r = τr′ + 2r‴; then 2x = τ²r′ + 2τr‴ = 2τr′ + 2e₂r′ + 2τr‴, and x ≡ e₂r′ mod τT.
  - Conversely 2e₂ = τ(τ − 2). Hence X[2] = e₂X and 2X ≅ X/X[2] = T/(τ, e₂)T. It fails on T(0), where F = 0 (Leg 0, control (d)).
- **Lemma H-odd — CORRECT.**
  - With T = Φ(N): exp F_T(b₀n) = b₀Ch(n) + b₁Sh(n), as in tilt_dp's Φ.
  - The sign of the target floor is ε on b₀ and −ε on b₁, so a(b₀n) = ε[b₀Ch(n) − b₁Sh(n)].
  - Sh is a unit, so T is free over Z₂[a] on b₀N, and b₁n = b₀ChSh⁻¹n − ε·a(b₀Sh⁻¹n).
  - τ commutes with a, so τ has matrix [[P, Q], [Q, P]] on (b₀N, a·b₀N), with P = ChSh⁻¹ + 2(2D_N + j) and Q = −εSh⁻¹.
  - On T/(a − 1)T ≅ N the cokernel is that of P + Q = 2(2D_N + j) + (Ch − ε)Sh⁻¹. No injectivity of τ is used, so it holds at j = 0.
- **Lemma H-even — CORRECT as gated.** Coinvariants of V ⊗ M under a are M. I did not re-derive the identification of τ with 1 + τ_ν − a_ν line by line; my own implementation of the printed formula matches the direct computation in every cell of λ ≤ 20, i ≤ 6, and its control fires.
- **Assembly (§3.1) — CORRECT.** Theorem RT, Lemma RT̄ and the closed rule give, for each n, a finite list of cells; the law for n is «X̄ = rule lowered by one» in those cells.

**No GAP and no ERROR in what was read.** Presentation slips:
- §2 A.4 names (3,2),(7,2),(3,2) as the «first» Borel failure. In the log the first one is (7,1),(5,2). Both fail; the auditor re-checked (7,1),(5,2).
- §9 reports that MISSION.md differs from its manifest. The change was the auditor's own (the rename «Kill criterion» → «Stop rule» at 12:52, MISSION v2 md5 `46c422b6…`). The pilot could not know it, and was right to report it.

## 4. Independent gates — engine `engines_gh/gh_audit_vuelo7.py`

The half-size formulas are implemented from their printed statements, not from the flight's code:
- H-odd by two routes (a matrix inverse of Sh, and a series division), checked equal;
- my own Smith form mod 2^192;
- my own rule (gh_audit_vuelo6);
- the only flight-6 code used is the lattice builder tilt_dp, validated in my mode L of 4 Oct.

Predictions sealed before any run in `SEALED_AUDITOR_7.md`.

| run | what | result | control |
|---|---|---|---|
| G 20 6 | H formulas = my direct coker[τ \| a − 1] = rule lowered, λ ≤ 20, i ≤ 6 | **140/140** | sign flipped: differs 140/140 |
| S 61–100, half-dim ≤ 128 | every such cell of every n = 61..100 | **1 358 cells, 0 failures** | — |
| S 61–100 step 3, half-dim ≤ 256 | | **546 cells, 0 failures** | — |
| S 62, S 94 | every cell of n = 62 (first half-dim 512) and n = 94 (first half-dim 1024, λ = 94) | **31/31, 47/47** | — |
| SF chain 61–75, 76–88, 89–93, 95–97, 98–100 (+ S 94) | **every cell of every n = 61..100**, half-dim up to 1024 | **1 573 + 47 cells, 0 failures: all 1 620 new cells computed a second time** | — |
| repro Borel | flight's `borel_lat.py 400 5 deep` on a copy | **identical log** (158 kept lattices, 24 fold failures) | — |
| my-Smith recheck | first Borel counterexample, strings (7,1),(5,2), i = 1 | X = {1², 2³, 9, 10}, **X̄ = {1, 2, 8, 9} ≠ 2X = {1³, 8, 9}** — confirmed | — |

Peaks: ≤ 801 MB; the longest run (n = 98..100) took 335 s. **So Theorem C₇ (n ≤ 100) rests on two independent exact computations of every cell.**

## 5. Sealed predictions of the auditor
S7.1, S7.2, S7.3, S7.5 held. S7.4 («smith_py at D = 256 in ≤ 30 s», the only one with real risk) held: 2 s on a random matrix, and the real cells were faster than feared.

## 6. The constructor's conduct
- **Rules kept:** no agents; one window (it re-entered once and says so); everything in its folder and through vigia; integers and fractions only.
- **Estimates were on disk before each leg and run** (the fault of flight 6, E1–E2, not repeated).
- **Failures published in full size:** PA.0, PL.f, PL.i, PB7.2, PB7.4, PB7.5, PC7.2.
- **Errors published:** E1–E4. E4 is the important one: a proof first marked PROVED and downgraded to SKETCH by the pilot itself.
- **Grade: HIGH MARK.** It did not close the target. It closed the range to n ≤ 100, gave the half-size formulas (a factor 2 in size and valid at shift 0), and above all it drew the line any proof must cross: the law is not formal.

## 7. What is open after this flight
1. **The fold law for every n.** Equivalent, family by family, to:
   - odd λ = 2λ₁ + 1: (P) on T(λ₁) for the series u·tanh(u/2) and u·coth(u/2) − 2;
   - even λ = ν + 1: coker(1 + τ − a) ≅ coker(τ(τ + 2)/2) on T(ν).
   - Flight 6's (Q), (Q_even) imply both.
2. **The obstruction named by the flight:** a perturbation-stable form of flights 3–4's Theorems O and F, i.e. of the very computation that proved the main rule.
3. Owed by the auditor from flight 6 (only needed if a route uses them): Ψ (Bernoulli coefficients), Lemma N, Lemma Z0, the §3.8 obstruction.
