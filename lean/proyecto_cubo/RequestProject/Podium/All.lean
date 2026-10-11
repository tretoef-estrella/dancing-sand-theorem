module

public import RequestProject.Podium.Defs
public import RequestProject.Podium.Clearings
public import RequestProject.Podium.Carries
public import RequestProject.Podium.Mean

/-!
# `C35_the_podium_arithmetic.md` — the podium arithmetic (Lemma 9.2, Lemma 9.5 and parts (M),
(K) of Proposition 9.6)

Folder `RequestProject/Podium/`, namespace `Podium`.  Nothing listed in the Setting is
redefined: C3 `Rulers.s2`, `v2`, `kappa`, `phi`, `oE`, `minOr`, `next` and `h` (through `h`),
`t1`, `hSum`, `lam`, `clock` and `proposition_5_3` are used directly; `Rulers.xi` and
`lemma_5_0_xi` enter only through `proposition_5_3` and are not needed by name.

## Encodings (`Defs.lean`)

* `k : ℕ`, `I : Finset ℕ`, `hI : I ⊆ Finset.range k`; `K = 2 ^ k`, `s = I.card`.
* `psi k I E : ℤ := Σ_{t ∈ E} ((Rulers.h k I t : ℤ) − 2 ^ t)` is `ψ(E)`.
* `P I l := I.filter (fun t => (I.filter (· < t)).card < l)` is `P_l`, the `l` smallest
  elements of `I`.
* `tAt k I l := Rulers.minOr k (I \ P I l)` is `t_{l+1}` (with `t_{s+1} = k`).
* `Y k I l := 2 ^ k + Rulers.oE (I \ P I l)` is `Y_l`.
* `clear N q := 2 ^ q * (N / 2 ^ q)` is `N` with its bits below `q` cleared.
* `φ`, `κ`, `ψ` and the clocks are integers; `i − 1` is natural-number subtraction (always used
  with `i ≥ 1`); the subsets `D ⊆ P_l` are `D ∈ (P I l).powerset`; `[2^q ≤ m mod 2^q + o]` is
  `if 2 ^ q ≤ m % 2 ^ q + o then 1 else 0`.

## Index

* **Part P** (`Defs.lean`): (P0) `P0`.
* **Part L** (`Clearings.lean`): (La) `La`; (Lb) `Lb_le`, `Lb`; (Lc) `Lc_Y_eq_clear`,
  `Lc_clear_eq_Y`, `Lc_Y_le_Y_one`, `Lc_clear_Y_one`; (Ld) `Ld`, `Ld_one`.
* **Part K** (`Carries.lean`): (K) `K`.
* **Part M** (`Mean.lean`, and `Carries.lean` for (M3)): (M1) `M1`; (M2) `M2`; (M3) `M3`;
  (M4) `M4`; (M5) `M5`.

## Hypotheses that are not needed

The statements are those of the file, sometimes more general:
* (P0) does not need `I ⊆ range k`, and `l ≤ s` is only used for `|P_l| = l`.
* (La), (Lc) first part, (M2) and (M4) hold for every `l` (the file assumes `l ≤ s`).
* (Lb): the hypothesis `N ≥ 1` follows from `1 ≤ y ≤ N` and is omitted.
* (Lc) third part (`Y_l ≤ Y_1` for `l ≥ 1`) needs neither `1 ≤ s`, `l ≤ s` nor `I ⊆ range k`.
-/
