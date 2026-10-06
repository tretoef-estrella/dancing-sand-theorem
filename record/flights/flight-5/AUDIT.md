# Audit — Flight 5 («Grepy el volador 5»: the two trophies), Grepy Hypercube, 4 Oct 2026

The delivery is copied with md5 into `reports/VOLADOR_5/ENTREGA_VUELO_5/` (manifest there; 28 files):
- REPORT.md `449fe18b79e1889c55b16cf7952dddbd`
- checks/SEALED.md `8f08238c…`
- logs/DIARY.md `af489664…`

## 1. Verdict in one line

**BOTH TROPHIES CLOSED.** The constructor proved, by pencil, the podium theorem (REPORT §4.1). From it follow:
- **Gao et al. Conjecture 4.14:** v₂ c_n(Q_n) = max(max_{x<n−1}(v₂x + x), v₂(n−1) + n − 3) for every n ≥ 3;
- **the JMM 2019 poster's (n+1)-th factor:** v₂ c_{n+1}(Q_n) = max_{x<n−1}(v₂x + x) for every n ≥ 4;
- Gao's Theorems 4.1 and 4.2 again, as the first n − 1 places (calibration passed).

**Grade.** PROVED by pencil. Each link was read twice, by its author and by this auditor, and passed my own gates (none of flight 5's code), with controls that fire.
- It rests on the closed rule (flights 1–4, audited 3 Oct).
- One step, the head lemma (H), is flight 4's Theorem F block structure. It is not re-proved here, but it is gated in 250 000 cells.
- No external cold reading yet.

## 2. Pencil reading (my own words; CORRECT / GAP / ERROR)

- **§1.1 absolute form — CORRECT.** B(μ, J) = μ + 1 + v₂(J·C(n−J, J)), and J·C(n−J, J) = (n−2J+1)·C(n−J, J−1). Hence u(D) = φ(x) + κ(J−1, x) + h(D), with x = n − 2J + 1.
- **F1 (i = 1) — CORRECT.** I re-derived the borrow count in M − o_D, M = 2^k − 1 + o_E:
  - below e = min E every bit is 1, so nothing borrows;
  - W_e is empty (bit e = 0, nothing arrives);
  - every window W_t with t ∈ D, t > e borrows out of all of its h_t bits;
  - a borrow is absorbed at a digit of E∖e or at k.
  
  So κ = h(D) − (e − t₁), and the case E = ∅ gives the same form.
- **F0, Fi — CORRECT** (the s₂ algebra).
- **(C) prefix identity, (R) Remark 4.4 — CORRECT.**
- **W1 consequences — CORRECT.**
  - The free walker ∅ reaches the max over the clearings of n − 1, which is g(n).
  - A dancer with a digit is capped at the centres l ≥ 1, the clearings of Y₁ ≤ n − 2, so it is ≤ g(n−1).
- **W0 — CORRECT after E2.** I re-derived:
  - antisymmetry about C_j (with min ∅ := t_{j+1});
  - the lower-half shift 2^{t_{j+1}} (and +(t_{j+1} − t_j) for ∅);
  - the final coordinates λ_j + 1 + S_j = n + 1, so the free dancer of level j sits at φ(n+1) + t_{j+1} − t₁. **The corrected index is right.**
  
  The trophies use only the top φ(Y′₁) − 2^{t₁} and the bound max_{l≥2} φ(Y′_l); both are gated below.
- **Theorem C, the ceiling — CORRECT given (H).**
  - (M): the average of 2τ(D) over the house is τ(P_l). The κ-difference splits cleanly to κ(m_h + c_D, Y_l/2^q): the low parts cancel, and s₂(Y_l + o_D) = s₂(Y_l/2^q) + s₂(o_D).
  - **Lemma K:** no carry is born below v₂B, so κ ≤ p − v₂B. A carry leaving bit p − 1 forces (A+B) mod 2^p < A mod 2^p ≤ A. The candidate y = 2^q·(A+B rounded down to 2^p) has φ(y) ≥ 2^q(B+1) + q + p > φ(2^qB) + κ. Strict, as claimed.
  - The range bound Y_l + 2^q(m_h + c_D) ≤ λ + 1 + m = n − i is right in both cases of c_D.
- **(H) — READ, not re-proved.** Flight 4's level structure gives a first block that is a dyadic house. The real cell is the base cell plus a shift that is constant on the blocks; if a merge happened, the max would still equal the house mean. **My gate: the first PAVA block is a dyadic house in 250 000 / 250 000 cells, so no merge occurs there.**
- **Multiplicities §2.4 — CORRECT** (Donkin's product formula, peeling at the three top weights).
- **Podium §4.1 — CORRECT, case by case.** In the even case 2(n−2) ≥ n copies of G is enough. At n = 4, V₀ = 5 > G = 3; at n = 6, V₀ = 6 = G is harmless.

**No GAP, no ERROR found.**

## 3. Independent gates — MEASURED, 0 failures

Engine `engines_gh/gh_audit_vuelo5.py`:
- raw clocks from flight 1's definition of B, and its Legendre form;
- my own integer PAVA (ceil first);
- my own multiplicities (gh_audit_vuelo2.py).

Every run ended VIGIA-FIN-OK, peak ≤ 47 MB, longest 82 s.

| mode | what | result | control (fires) |
|---|---|---|---|
| A | absolute form vs B (sum and Legendre), λ + 2i ≤ 300 | 220 767 cells, 0 | F + \|D\| breaks in 198 267 |
| C | ceiling g(n−i+1) + head is a dyadic house, λ + 2i ≤ 1000, i ≥ 1 | 250 000 cells, 0 | ceiling g(n−i) exceeded in 999; top = u(∅) wrong in 59 585 |
| W | W1 (∅ = g(n), rest ≤ max_{l≥1} φ(Y_l) ≤ G, {0} = G for even n); W0 (top formula, rest ≤ max_{l≥2} φ(Y′_l) ≤ G, V₀ by t₁); odd n: family n−4 at i = 2, ∅ = G; m_n, m_{n−2}, m_{n−4} | n ≤ 600, 0 | — |
| K | Lemma K, A < 256, 1 ≤ B < 256, q ≤ 3, with strictness | 261 120 cases, 0 | range shortened by 2^q fires 565 |
| P | podium from scratch (whole multiset), T1, T2, Gao 4.1, 4.2, the four cases | n ≤ 1000, 0 (cases: even 499; odd φ ≤ G 146; odd G < φ 166; odd φ−2 > G 186) | «c_n = G always» fails at 186 |

Logs: `logs/gh_audit_vuelo5_{A,C,W,P}.log`, `logs/gh_audit_vuelo5_{C,P}_wide.log`, `logs/gh_audit_vuelo5_K_smoke.log`.

## 4. The constructor's conduct

- **Rules kept.** No agents, no workflows. `material/` and `MISSION.md` were verified unchanged. Everything is in its own folder.
- **Errors published:**
  - E2: the walk W0 index; its sealed prediction S3 FAILED, in the same type;
  - E3: a run killed by the watchdog, kept and not counted;
  - E1: a typed time;
  - E4: pencil done before it was put on disk, and estimates written after the pencil;
  - E5: missing diary lines.
  
  E4 and E5 break Rafa's «save as you go». No result is affected, but the next mission repeats the order louder.
- **Marks:** S3 failed honestly; S3-fix and S11 are graded as post-hoc. Grade of the work: **HIGHEST MARK.**

## 5. State of the art (4 Oct)

- One extended web search, for proofs of Conj. 4.14 or the poster's factor, found only Gao et al. (arXiv:1912.06919 v3; Comm. Algebra 2024), where 4.14 is open.
- **Credit:** Gao et al.'s method (φ(x) = v₂x + x, Remark 4.4) is the source of the candidates; the flight shows that they are the centres of the rule's reflected walk.

## 6. Open after this flight

- The closed form of the shift-2 clocks for λ ≡ 2 (mod 4) (not needed).
- The run of G beyond place n + 1.
- **Gao et al. Conjecture 5.4 and the fold law** — the next mission.
- The novelty sweep of Theorem D (auditor, in parallel).
- A cold reader for the whole chain.
