# Part 1 notes (first pass) — cold reader 8

Word diff v5→v6 (`logs/worddiff.log`, script `scratch/py/worddiff.py`): 18 hunks.
1 header date/version; 2 §1.0 record; 3 §1.7 «Why dance»; 4 §4.2 proof (Eliminating these relations (one for each n and s')); 5 §9.2 Prop 9.6 (H) proof, «the child» → fit(x_{H'}); 6 §10.1 exp F → exp(F); 7 §10.2 cosh u → cosh(u); 8 §10.4 «by subadditivity» moved; 9 §10.7 [½ → [1/2; 10–12 §12.2 cells; 13 §13 first two bullets; 14 §13 v5/v6 bullets; 15 §13 not done; 16 App. A v5/v6; 17–18 «Paper No.».

First suspicions:
- S1 §13 bullet 2: «no other statement of a theorem changed in versions 2 to 6» followed at once by «In version 3, Lemma 7.9 was strengthened, Lemma 10.6(a) gained the hypothesis «even», Lemma 10.10 gained the quantifier». The same sentence counts Lemma 7.2(b) as a statement of a theorem. To judge in Part 4.
- S2 Acknowledgements: «The work took four days, from 2 to 5 October 2026», while version 6 and reading 7 are dated 6 October. Check whether v5 said the same (unchanged line) and judge.
- S3 (p. 46) reader 3's «all houses with k ≤ 7, α = 1, 2: 43 690 houses» = 2 · Σ_{k=0}^{7} 4^k (k = 0 included), while «every house with k ≤ 7, α ≤ 3 (65 532)» = 3 · Σ_{k=1}^{7} 4^k (k = 0 excluded; by §7.3 a house with k = 0 exists: I = ∅, ℓ = 0). Degenerate houses only; taste list.
- S4 (p. 46) reader 3's «Theorems D and 7.10 on the lattices T(λ), λ ≤ 63, i ≤ 8, α = 1, 2: 1 401 cells» — 1 401 is odd, so it is not a product over α = 1, 2; the range as printed does not determine it. To look at in read_after (gates) if the reader's code is there.
- S5 to recount myself: the cells «where pooling acts/changes them»: 322 (§12.1, λ < 64, i ≤ 12, α = 1, 2), 1 876 and 1 834 with i ≥ 1 (λ ≤ 127, i ≤ 30, α = 1, 2), 274 (λ ≤ 63, i ≤ 8); and the controls 1 942 of 16 380 houses, 2 316 of 9 880 cells.
