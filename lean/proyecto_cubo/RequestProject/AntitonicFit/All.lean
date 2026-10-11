module

public import RequestProject.AntitonicFit.Basic
public import RequestProject.AntitonicFit.Characterization
public import RequestProject.AntitonicFit.IntegerFit
public import RequestProject.AntitonicFit.Cuts
public import RequestProject.AntitonicFit.Examples
public import RequestProject.AntitonicFit.Antisymmetry
public import RequestProject.AntitonicFit.Gluing

/-!
# Antitonic fits (`C1_antitonic_fits.md`)

Index of the formalization (namespace `AntitonicFit`):

* `Basic.lean` — encoding of sequences, `fit`, statement **(0)** (`existsUnique_fit`).
* `Characterization.lean` — level sets, **Lemma 7.1** (`lemma_7_1`).
* `IntegerFit.lean` — the integer fit `ifit`, consequence **(L)** (`consequence_L`).
* `Cuts.lean` — cuts, **(D)** (`consequence_D_cut`, `consequence_D_strict_iff`),
  **Lemma 7.2** (`lemma_7_2_a`, `lemma_7_2_b1`, `lemma_7_2_b2`, `lemma_7_2_b3`,
  `lemma_7_2_b3_b2`, `lemma_7_2_c`).
* `Examples.lean` — the example `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)`
  (`example_b2_hypothesis_needed`), and the other examples of the file.
* `Antisymmetry.lean` — **(A1)**, **(A2)**, **(A3)** (`A1`, `A2`, `A3`).
* `Gluing.lean` — **Lemma 7.3** (`lemma_7_3_Z2`, `lemma_7_3_fit`, `lemma_7_3_ifit`).
-/
