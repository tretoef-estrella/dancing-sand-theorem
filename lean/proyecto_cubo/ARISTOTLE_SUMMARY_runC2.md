# Summary of changes for run e0b97d3b-de3a-4859-8c1a-411333ea68b2
I formalized and proved every statement of `C2_smith_bounds.md` in the new folder `RequestProject/SmithBounds/`, in namespace `SmithBounds`. The whole project builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem. I did not touch `RequestProject/AntitonicFit/`.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `TropicalBound.lean`, **Part A**: `lemma_A1` and `lemma_A2`.
- `LeastTerm.lean`, **Part B**: `lemma_B` and `corollary_B'`.
- `Convexity.lean`, **Part C**: `lemma_C0_total` (\(Y(N)=U(N)\)), `lemma_C0` (the general form) and `lemma_6_4`. These are built on `AntitonicFit.ifit`, and Lemma C0 is proved from `AntitonicFit.consequence_L`.
- `TheoremU.lean`, **Part D**: `lemma_D0` and `theorem_U`.
- `Basic.lean`: the shared sum over the last \(r\) positions.

**Encodings** (also given in the module docstrings):
- **Minor `M[A,B]`:** `minor M e f = M.submatrix (e ·) (f ·)`. Here `e : Fin r ≃ A` lists the rows and `f : Fin r ≃ B` lists the columns, so these are the "fixed orders". Every result holds for every choice of `e` and `f`.
- **Matchings (Part A):** an `A→B` matching is an equivalence `β : A ≃ B` with `supp a (β a)`. Its cost is \(\sum_{a\in A} c(a,\beta a)\).
- **`U(r)`, `Y(r)`:** sums over `Finset.Ico (N - r) N` (the last \(r\) positions), of `x` and of `ifit N x` respectively.
- **Convexity:** `d : ℕ → ℤ` (only values at \(r \le N\) matter) is convex if \(d(r+1)-d(r) \le d(r+2)-d(r+1)\) whenever \(r+2 \le N\).
- **First position of a level set:** "`N − r` starts a level set of `fit(x)`" is written as `∃ q, IsLevelInterval N (fit N (toR x)) (N - r) q`.
- **`r`-matchings (Part D):** a set `Rows ⊆ {0,…,N−1}` with `|Rows| = r`, plus a map `β : ℕ → ℕ` that is injective on `Rows`, takes values `< N` there, and satisfies `arr a (β a)`.

**Where the statements differ slightly from the file** (all noted in the docstrings):
- **More general:**
  - In Part A the index type `n` need not be finite.
  - In Theorem U, condition (U3) is only assumed for arrows between positions `< N`, as the file says.
- **Unused hypotheses:**
  - In Lemma B, the hypothesis `p ≥ 2` is kept because you asked for it, but the proof does not need it.
  - In Corollary B′, the setting hypothesis \(p^{c(a,b)} \mid M\,a\,b\) is kept but is likewise not used.
- **Encoding of "exactly one matching of least cost `T`":** `β₀` is a matching of cost `T`, and every other matching costs more than `T`.

**A note on the proof of Lemma 6.4:** for each level set I used a shorter version of the paper's argument. Inside a level set the steps of \(Y\) are always \(q\) or \(q+1\), and \(Y = U\) at both ends of the level set (Lemma C0). Those two facts plus convexity are enough. The case split on \(r^* \le r_0+p-\rho\) is not needed, and neither is the order of the ceilings and floors inside the level set. This agrees with the file's note that putting the floors first only weakens the lemma.

The Properties table lists these results as proved, together with the definitions they use.

# Summary of changes for run 2b8cfa39-a66a-4a5d-9647-f3cb847d0e82
I formalized and proved in Lean 4 with Mathlib every statement of `C1_antitonic_fits.md`. All files are in `RequestProject/AntitonicFit/`, in namespace `AntitonicFit`. Everything builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem.

**Encoding** (described in the module docstrings of `Basic.lean`, `Characterization.lean` and `IntegerFit.lean`):
- **Sequences:** a sequence of length `N` is a function `ℕ → ℝ`. Every notion only reads the positions below `N`, so equality of sequences is stated as `∀ j < N, …`.
- **Prefix, suffix, concatenation:** the prefix \(x_{<b}\) is the same function used with length `b`. The suffix \(x_{\ge b}\) is `shift b x = fun j => x (b + j)`, used with length `N - b`. The concatenation `[u, v]` is `concat M u v = fun j => if j < M then u j else v (j - M)`.
- **Mirror-negative and antisymmetry:** \(u^*\) is `mirror M u = fun j => -u (M-1-j)`, and `IsAntisymm N x` says `x (N-1-j) = -x j` for every `j < N`.
- **Level sets:** `levelSet N z j = {i < N : z i = z j}`. `IsLevelInterval N z p q` says that `[p, q]` is a level set. I also proved that for a non-increasing `z` every level set is such an interval.
- **`fit`:** defined as a non-increasing minimizer of \(\sum_j (x_j - z_j)^2\), chosen using the existence half of (0) and set to `0` at positions `≥ N`. It is not defined by an algorithm.
- **`ifit`:** integer sequences are `ℕ → ℤ`. On the level set `L` of `j` in `fit(x)`, with \(P = |L|\) and \(S = \sum_L x\), the value is \(\lceil S/P\rceil\) if the rank of `j` in `L` is below `S % P` (the non-negative remainder), and \(\lfloor S/P\rfloor\) otherwise. A lemma checks that the rank is `j − p` when `L = [p, q]`, which is exactly the rule in the file. Nothing claims `ifit` is non-increasing.

**Results** (each docstring names its part of the file):
- **(0):** `existsUnique_fit`.
- **Lemma 7.1:** `lemma_7_1`, the "iff" with the two level-set conditions.
- **(L):** `consequence_L`.
- **(D):** `consequence_D_cut` and `consequence_D_strict_iff`.
- **Lemma 7.2:** `lemma_7_2_a`, `lemma_7_2_b1`, `lemma_7_2_b2`, `lemma_7_2_b3` (plus `lemma_7_2_b3_b2`, which applies (b2)) and `lemma_7_2_c`. In (b1), the cut positions \(b_1 < \dots < b_s\) are a `Finset` `B`. "Constant on each interval between cuts" is written as \(\delta_{j+1} = \delta_j\) whenever `j+1 ∉ B`, which is equivalent.
- **Example `x = (3,4,3,4)`, `δ = (1,1,0,0)`:** `example_b2_hypothesis_needed` proves that `x` is cut at 2, the cut is not strict, and `ifit(x+δ) ≠ ifit(x)+δ` (they differ at position 1). I also proved \(\mathrm{fit}(x) = (7/2,7/2,7/2,7/2)\), \(\mathrm{ifit}(4,5,3,4) = (5,4,4,3)\), \(\mathrm{ifit}(x) = (4,4,3,3)\) and \(\mathrm{ifit}(x)+\delta = (5,5,3,3)\).
- **Antisymmetry:** `A1`, `A2`, `A3`. More generally, `fit_mirror` and `ifit_mirror` show that `fit` and `ifit` commute with mirror-negation for every sequence.
- **Lemma 7.3:** `lemma_7_3_Z2` (\(Z_2 = \mathrm{fit}(x_{\ge N'})\)), `lemma_7_3_fit` and `lemma_7_3_ifit`. The length \(2N'\) is written `2 * M`.
- **Other examples in the file** (in `Examples.lean`): `x = (−2,−2,0,−2,−1)` with its `fit` and `ifit` values, plus a proof that this `ifit` is not non-increasing; and the antisymmetric check `x = (2,−1,1,−2)`.

**Two statements are more general than in the file** (both noted in their docstrings):
- **(b2):** the hypotheses about the cuts \(b_i\), and about `δ` being constant between them, are dropped. The proof does not need them, because they follow from the remaining hypotheses.
- **(b3):** the first statement allows `δ` to take values in any type, not only integers.

`RequestProject/AntitonicFit/All.lean` imports everything and lists where each statement is. The Properties table lists these results, all marked proved.