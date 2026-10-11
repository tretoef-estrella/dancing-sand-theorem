# Antitonic fits: characterization, cuts and shifts, antisymmetric gluing

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §7.1, Lemmas 7.1–7.3. This file is self-contained.

## Setting

All sequences are finite sequences of real numbers indexed by positions `0, 1, …, N−1` (`N ≥ 0`). For a sequence `x` of length `N` and `0 ≤ b ≤ N`, write `x_{<b} := (x_0, …, x_{b−1})` and `x_{≥b} := (x_b, …, x_{N−1})`. Concatenation is written `[u, v]`.

A sequence `z` is **non-increasing** if `z_i ≥ z_{i+1}` for every `i`. For a non-increasing `z`, the **level set** of a position `j` is `{i : z_i = z_j}`. Since `z` is non-increasing, every level set is an interval `[p, q]` of consecutive positions.

**Definition (antitonic fit).** For a sequence `x` of length `N`, its **antitonic fit** `fit(x)` is the non-increasing sequence `z` that minimizes `‖x − z‖² = Σ_j (x_j − z_j)²` among all non-increasing sequences of length `N`.

**Definition (integer fit).** Let `x` be a sequence of integers and `z := fit(x)`. By the Lemma below, on each level set `[p, q]` of `z`, with `P := q − p + 1` positions, the sum `S := Σ_{j=p}^{q} x_j` is an integer and `S = P·z_p`. The **integer fit** `ifit(x)` takes, on each such level set, the values `⌈S/P⌉` at the first `S mod P` positions (`p, …, p + (S mod P) − 1`) and `⌊S/P⌋` at the remaining `P − (S mod P)` positions. Here `S mod P ∈ {0, …, P−1}` is the non-negative remainder.

The integer fit is NOT claimed to be non-increasing in general. For example, `x = (−2, −2, 0, −2, −1)` has `fit(x) = (−4/3, −4/3, −4/3, −3/2, −3/2)` and `ifit(x) = (−1, −1, −2, −1, −2)`.

**Definition (cuts).** Let `0 < b < N`. The sequence `x` is **cut at `b`** if `fit(x) = [fit(x_{<b}), fit(x_{≥b})]`. The cut is **strict** if moreover `fit(x)_{b−1} > fit(x)_b`.

**Definition (antisymmetric).** A sequence `x` of length `N` is **antisymmetric** if `x_{N−1−j} = −x_j` for every `j`. For a sequence `u` of length `M`, its **mirror-negative** is `u^*_j := −u_{M−1−j}`.

## Statements

**(0) Existence and uniqueness.** For every `x`, a non-increasing minimizer of `‖x − z‖²` exists and is unique. (It is the projection onto a closed convex cone of `ℝ^N`.)

**Lemma 7.1 (characterization).** A non-increasing sequence `z` equals `fit(x)` if and only if, for every level set `[p, q]` of `z`:
- `Σ_{j=p}^{q} (x_j − z_j) = 0`, and
- `Σ_{j=p}^{s} (x_j − z_j) ≤ 0` for every `p ≤ s ≤ q`.

**Consequences used below.**
- (L) If `x` is an integer sequence, then on every level set `[p, q]` of `fit(x)` the sum `S = Σ_{j=p}^q x_j` is an integer and equals `(q − p + 1)·fit(x)_p`. So `ifit(x)` is well defined, and its sum over each level set of `fit(x)` equals `S`.
- (D) If `fit(x)_{b−1} > fit(x)_b`, then `x` is cut at `b`. Hence `b` is a strict cut if and only if no level set of `fit(x)` contains both `b − 1` and `b`.

**Lemma 7.2 (cuts and shifts).**

(a) If `[fit(x_{<b}), fit(x_{≥b})]` is non-increasing, then `x` is cut at `b`.

(b) Let `x` be cut at the positions `b_1 < ⋯ < b_s` (`s ≥ 0`), and let `δ` be a non-increasing sequence of length `N` that is constant on each of the intervals `[0, b_1)`, `[b_1, b_2)`, …, `[b_s, N)`. Then:
- (b1) `fit(x + δ) = fit(x) + δ`, and `x + δ` is cut at each `b_i`.
- (b2) Suppose moreover that `x` and `δ` are integer sequences, and that `δ` is constant on every level set of `fit(x)`. Then the level sets of `fit(x + δ)` are exactly those of `fit(x)`. Every strict cut of `x` is a strict cut of `x + δ`. And `ifit(x + δ) = ifit(x) + δ`.
- (b3) If `δ` is integer and every position `b` with `δ_{b−1} ≠ δ_b` is a strict cut of `x`, then `δ` is constant on every level set of `fit(x)`. So (b2) applies.

(c) If `fit(x)_{<b} = fit(x_{<b})`, or `fit(x)_{≥b} = fit(x_{≥b})`, then `x` is cut at `b`.

**The hypothesis of (b2) cannot be dropped.** Take `x = (3, 4, 3, 4)` and `δ = (1, 1, 0, 0)`. Then:
- `fit(x) = (7/2, 7/2, 7/2, 7/2)`, so `x` is cut at `2`, but not strictly.
- `ifit(x + δ) = ifit(4, 5, 3, 4) = (5, 4, 4, 3)`.
- `ifit(x) + δ = (4, 4, 3, 3) + δ = (5, 5, 3, 3)`.

Please also prove these three facts about this example: `x` is cut at 2, the cut is not strict, and the two integer fits differ.

**Antisymmetry.** Let `x` be antisymmetric of length `N`. Then:
- (A1) `fit(x)` is antisymmetric.
- (A2) If `x` is an integer sequence, `ifit(x)` is antisymmetric.
- (A3) For `0 < b < N`, `x` is cut at `b` if and only if it is cut at `N − b`, and the cut at `b` is strict if and only if the cut at `N − b` is.

**Lemma 7.3 (antisymmetric gluing).** Let `x` be antisymmetric of length `2N'`. Let `Z_1 := fit(x_{<N'})`, and when `x` is an integer sequence let `X_1 := ifit(x_{<N'})`. Let `Z_2 := Z_1^*` and `X_2 := X_1^*` be their mirror-negatives. Then:
- `Z_2 = fit(x_{≥N'})`;
- `fit(x) = [max(Z_1, 0), min(Z_2, 0)]`, with max and min taken entrywise;
- if `x` is an integer sequence, `ifit(x) = [max(X_1, 0), min(X_2, 0)]`.

## Proofs (from the paper)

**(0).** The non-increasing sequences form a closed convex cone in `ℝ^N`; the Euclidean projection onto a closed convex set exists and is unique.

**Lemma 7.1.**
- *Necessity.* Suppose some prefix of a level set had a positive sum. Raise the values on that prefix by a small `ε` and lower the rest of the level set by a suitable amount. The result is still non-increasing and closer to `x`. The same argument applies if the total over the level set is non-zero.
- *Sufficiency.* Let `y` be non-increasing. Then
  `‖x − y‖² = ‖x − z‖² + ‖z − y‖² + 2 Σ_j (x_j − z_j)(z_j − y_j)`.
  Take a level set `[p, q]` with value `c`, and put `S_s := Σ_{j=p}^{s}(x_j − c)`; so `S_s ≤ 0` and `S_q = 0`. Abel summation gives
  `Σ_{j=p}^{q}(x_j − c)(c − y_j) = −Σ_{s=p}^{q−1} S_s (y_s − y_{s+1}) ≥ 0`,
  because `y` is non-increasing. So `‖x − y‖ ≥ ‖x − z‖`, and by uniqueness `z = fit(x)`.

**(L)** is the first condition of Lemma 7.1. **(D):** Lemma 7.1 is a condition on each level set separately. When `fit(x)` drops strictly at `b`, its level sets lie entirely on one side of `b`, so the two pieces of `fit(x)` satisfy Lemma 7.1 for `x_{<b}` and `x_{≥b}`.

**Lemma 7.2.**
- (a) Each level set of the concatenation is either a level set of one piece, or the union of a final level set of the first piece and an initial level set of the second piece, with the same value. Lemma 7.1 for the pieces gives it for the union: a prefix that crosses `b` has the total `0` of the first part plus a prefix sum `≤ 0` of the second.
- (b1) On each piece between cuts, the fit of `x + const` is the fit of `x` plus that constant. The concatenation of the shifted fits is `fit(x) + δ`, which is non-increasing because `fit(x)` and `δ` are. Apply (a) repeatedly.
- (b2) Take two adjacent level sets of `fit(x)`, with values `μ_A > μ_B`. They receive constants `δ_A ≥ δ_B`, so `μ_A + δ_A > μ_B + δ_B`. Hence the level sets of `fit(x) + δ` are those of `fit(x)`, and a strict drop stays strict. On a level set of `P` positions with sum `S`, adding the integer `δ_L` everywhere adds `P·δ_L` to the sum. This keeps `S mod P` and adds `δ_L` to both `⌈S/P⌉` and `⌊S/P⌋`.
- (b3) A level set never contains the two sides of a strict cut.
- (c) Let `z := fit(x)` agree with `fit(x_{<b})` before `b`. Let `L = L_1 ∪ L_2` be a level set of `z`, with value `c`, that crosses `b` (`L_1` before `b`). Then `L_1` is a final level set of `fit(x_{<b})`, so `Σ_{L_1}(x − c) = 0`. Hence the sum of `x − c` over a prefix of `L_2` equals its sum over `L_1` plus that prefix, which is `≤ 0` by Lemma 7.1 for `z`; and the total over `L_2` is `0`. The level sets of `z` after `b` are unchanged, so `z_{≥b}` satisfies Lemma 7.1 for `x_{≥b}`, and `z_{<b} = fit(x_{<b})` by hypothesis. The second hypothesis reduces to the first by reversing and negating the sequence.

**Antisymmetry.**
- (A1) Reversal plus negation maps non-increasing sequences to non-increasing sequences and preserves distances, so it commutes with `fit` by uniqueness.
- (A2) A level set of size `P` and sum `S` is mirrored to one of size `P` and sum `−S`. The rule there gives `P − (S mod P)` copies of `−⌊S/P⌋` followed by `(S mod P)` copies of `−⌈S/P⌉`, the mirror-negative of the original block. (When `S mod P = 0` both blocks are constant.)
- (A3) follows from (A1) and the definitions.

**Lemma 7.3.** The candidate `z := [max(Z_1, 0), min(Z_2, 0)]` is non-increasing. Its level sets are three kinds:
- the level sets of `Z_1` with positive value;
- their mirrors;
- one central level set `P ∪ P^*` with value `0`. Here `P = {j < N' : Z_1(j) ≤ 0}` is a final segment of the first half and a union of level sets of `Z_1`, and `P^*` is its mirror.

Now check Lemma 7.1 on each kind:
- The positive level sets satisfy Lemma 7.1 because they do for `Z_1`; their mirrors do by antisymmetry.
- On `P ∪ P^*` the total of `x` is `0`, by antisymmetry.
- A prefix contained in `P` has sum at most the corresponding sum of `Z_1`, by Lemma 7.1 applied to the level sets of `Z_1` that it covers; and that sum is `≤ 0`.
- A prefix that covers `P` and the first `L` positions of `P^*` has sum `Σ_P x − Σ_{last L positions of P} x`. This is the sum over the first `|P| − L` positions of `P`, which is `≤ 0` again.

So `z = fit(x)`. The integer fit takes, on the positive level sets, the same values as `X_1`, and `0` on the central level set. Moreover `X_1 ≥ 0` where `Z_1 > 0`, and `X_1 ≤ 0` where `Z_1 ≤ 0`. `Z_2 = fit(x_{≥N'})` holds by (A1) applied to the reversal-negation of `x_{<N'}`, which is `x_{≥N'}`.

## Checks (computed independently, exact rational arithmetic)

- `fit(3, 4, 3, 4) = (7/2, 7/2, 7/2, 7/2)`; `ifit(4, 5, 3, 4) = (5, 4, 4, 3)`; `ifit(3, 4, 3, 4) = (4, 4, 3, 3)`.
- `fit(−2, −2, 0, −2, −1) = (−4/3, −4/3, −4/3, −3/2, −3/2)`; `ifit(−2, −2, 0, −2, −1) = (−1, −1, −2, −1, −2)`.
- Antisymmetric example: `x = (2, −1, 1, −2)` gives `Z_1 = fit(2, −1) = (2, −1)`, so `fit(x) = (2, 0, 0, −2)`.
- A brute force over all integer sequences of length ≤ 6 with small entries, and 20 000 random rational sequences of length ≤ 12, found no failure of (0), 7.1, (D), 7.2(a), (b1)–(b3), (c), (A1)–(A3) or 7.3. The false variants of 7.2(b2) without its hypothesis, and of 7.3 with max and min swapped, fail, as they should.
