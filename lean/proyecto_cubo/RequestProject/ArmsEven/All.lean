module

public import RequestProject.ArmsEven.Defs
public import RequestProject.ArmsEven.PartP
public import RequestProject.ArmsEven.PartA
public import RequestProject.ArmsEven.PartH
public import RequestProject.ArmsEven.PartC
public import RequestProject.ArmsEven.PartE

/-!
# `C50c_the_arms_of_the_even_families.md` (paper v8 §10.7, Theorem 10.22 first part; Corollary 10.21)

Namespace `ArmsEven`. Every part of the file:

* `Defs.lean`: the new definitions `uSys`, `eI`, `GPsi` (nothing listed in the Setting is
  redefined);
* `PartP.lean`: (P1) `P1`; (P2) `P2`; (P3) `P3`;
* `PartA.lean`: (A1) `A1`;
* `PartH.lean`: (H1) `H1`; (H2) `H2`;
* `PartC.lean`: (C1) `C1`;
* `PartE.lean`: (E1) `E1`; (E2) `E2`.

No statement needed a hypothesis that the file does not give. In (H2) the hypotheses of (H1)
(`Good Γ`, `ε = 1 ∨ ε = -1`) are kept, as anonymous binders, although the proof does not use them.
The abbreviations of the file (`Sys`, `e∅`, and `c`, `Γ₁`, `Γ₀` in (E1), (E2)) are written out in
full in the statements.
-/
