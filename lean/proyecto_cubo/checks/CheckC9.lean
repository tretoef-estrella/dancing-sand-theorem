import RequestProject.CellFloor.All

/-! Auditor's check file for Lean piece C9 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C9_integrality_and_cell_floor.md` and closed by `rfl`; the main
statements restated by hand with the definitions unfolded and closed by the certified theorems;
then `#print axioms`. -/

open CellFloor TheoremF Potential AntitonicFit SmithBounds Finset

-- Encodings (Setting)
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (Pr Pc p : ℕ) :
    cellClock I k ℓ α Pr Pc p = xHseq I k ℓ α p - (Pr : ℤ) * (JHseq I k ℓ p : ℤ)
      + (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - p) : ℤ) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (Pr Pc p q : ℕ) :
    cellCost I k ℓ α Pr Pc p q = Houses.cHatH I k ℓ α (dancer I p) (dancer I q)
      - (Pr : ℤ) * (JHseq I k ℓ p : ℤ) + (Pc : ℤ) * (JHseq I k ℓ q : ℤ) := rfl
example (I : Finset ℕ) (p q : ℕ) :
    IsCellArrow I p q ↔ p < 2 ^ #I ∧ q < 2 ^ #I ∧ dancer I q ⊆ dancer I p := Iff.rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (j : ℕ) : xSharp I k ℓ α j = xHseq I k ℓ α (j + 1) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) :
    yhatSharp I k ℓ α = ifit (2 ^ #I - 1) (fun j => xHseq I k ℓ α (j + 1)) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (a b : ℕ) :
    costSharp I k ℓ α a b = Houses.cHatH I k ℓ α (dancer I (a + 1)) (dancer I b) := rfl
example (I : Finset ℕ) (a b : ℕ) :
    IsSharpArrow I a b ↔ a < 2 ^ #I - 1 ∧ b < 2 ^ #I - 1 ∧ dancer I b ⊆ dancer I (a + 1) := Iff.rfl

-- Lemma 7.9 (I1): the real fit of x_H is integral and equals ŷ_H
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∀ p < 2 ^ #I, fit (2 ^ #I) (fun r => ((xHseq I k ℓ α r : ℤ) : ℝ)) p =
      ((ifit (2 ^ #I) (xHseq I k ℓ α) p : ℤ) : ℝ) :=
  (lemma_7_9_I1 hI hℓ hα).1

-- Lemma 7.9 (I2), written out
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α)
    (Pr Pc : ℕ) : ∀ p < 2 ^ #I,
      ifit (2 ^ #I) (fun r => xHseq I k ℓ α r - (Pr : ℤ) * (JHseq I k ℓ r : ℤ)
        + (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - r) : ℤ)) p =
      ifit (2 ^ #I) (xHseq I k ℓ α) p - (Pr : ℤ) * (JHseq I k ℓ p : ℤ)
        + (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - p) : ℤ) :=
  (lemma_7_9_I2 hI hℓ hα Pr Pc).1

-- Theorem B, the floor of a cell (T(r) ≥ Y(r)), written out
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α)
    (Pr Pc : ℕ) {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I) (fun p q => p < 2 ^ #I ∧ q < 2 ^ #I ∧ dancer I q ⊆ dancer I p)
      r Rows β) :
    tailSum (2 ^ #I) r (fun j => (ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) j : ℝ)) ≤
      ∑ a ∈ Rows, (cellCost I k ℓ α Pr Pc a (β a) : ℝ) :=
  theorem_B_floor hI hℓ hα Pr Pc hm

-- Theorem C, the shift 0
example {I : Finset ℕ} {k : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hα : 1 ≤ α) (hne : I.Nonempty)
    {r : ℕ} {Rows : Finset ℕ} {β : ℕ → ℕ}
    (hm : IsRMatching (2 ^ #I - 1)
      (fun a b => a < 2 ^ #I - 1 ∧ b < 2 ^ #I - 1 ∧ dancer I b ⊆ dancer I (a + 1)) r Rows β) :
    tailSum (2 ^ #I - 1) r (fun j => (ifit (2 ^ #I - 1) (fun j => xHseq I k (2 ^ k - 1) α (j + 1)) j : ℝ)) ≤
      ∑ a ∈ Rows, (Houses.cHatH I k (2 ^ k - 1) α (dancer I (a + 1)) (dancer I (β a)) : ℝ) :=
  theorem_C_floor hI rfl hα hne hm

#print axioms ifit_eq_of_fit_eq_int
#print axioms lemma_7_9_I1
#print axioms lemma_7_9_I2
#print axioms lemma_7_9_I3
#print axioms theorem_B_U1
#print axioms theorem_B_U2
#print axioms theorem_B_U3
#print axioms theorem_B
#print axioms theorem_B_floor
#print axioms theorem_C
#print axioms theorem_C_floor
