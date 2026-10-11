import RequestProject.Potential.All

/-! Auditor's check file for Lean piece C8 (Grepy Escribano, 6 Oct 2026).
Encodings written out by hand from `C8_theorem_F_potential.md` and closed by `rfl`; the main
statements restated by hand with the definitions unfolded and closed by the certified theorems;
then `#print axioms`. -/

open Potential TheoremF Finset AntitonicFit

-- Encodings (Setting and Part 1 of the file)
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : yhat I k ℓ α = ifit (2 ^ #I) (xHseq I k ℓ α) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (p q : ℕ) :
    cHat I k ℓ α p q = Houses.cHatH I k ℓ α (dancer I p) (dancer I q) := rfl
example (I : Finset ℕ) (p q : ℕ) :
    IsArrow I p q ↔ p < 2 ^ #I ∧ q < 2 ^ #I ∧ dancer I q ⊂ dancer I p := Iff.rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c p : ℕ) :
    X1 I k ℓ α c p = ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) p
      + Houses.d1 I k ℓ α c (dancer (I.erase c) p) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (p : ℕ) (hp : p < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' p = V' p - (if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0) *
      (Houses.JH c (ℓ % 2 ^ c) (dancer (I.erase c) p) : ℤ) := vPrime_low α c V' hp
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (p : ℕ) :
    vPrime I k ℓ α c V' (2 ^ #(I.erase c) + p) = Houses.tau I k ℓ α c + V' p -
      (if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0) *
        (Houses.JH c (ℓ % 2 ^ c) (dancer (I.erase c) p) : ℤ) := vPrime_high α c V' p
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) (cF : ℤ) (p : ℕ) :
    flatV I k ℓ α c V' f cF p = if f ≤ p ∧ p ≤ 2 ^ #I - 1 - f then cF else vPrime I k ℓ α c V' p :=
  rfl

-- Theorem F (Theorem 7.8), the potential written out
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∃ V : ℕ → ℤ,
      (∀ p < 2 ^ #I, V p - V (2 ^ #I - 1 - p) =
        ifit (2 ^ #I) (fun r => Houses.xH I k ℓ α (dancer I r)) p) ∧
      (∀ p q, p ≤ q → q < 2 ^ #I → V q ≤ V p) ∧
      (∀ p q, p < 2 ^ #I → q < 2 ^ #I → dancer I q ⊂ dancer I p →
        V p - V q ≤ Houses.cHatH I k ℓ α (dancer I p) (dancer I q)) := by
  obtain ⟨V, hV⟩ := theorem_F hI hℓ hα
  exact ⟨V, hV.E, hV.M, fun p q hp hq hs => hV.G p q ⟨hp, hq, hs⟩⟩

-- Corollary F′ (on subsets)
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∃ W : Finset ℕ → ℤ,
      (∀ D, D ⊆ I → W D - W (I \ D) =
        ifit (2 ^ #I) (fun r => Houses.xH I k ℓ α (dancer I r)) (GoldenMatching.rank I D)) ∧
      (∀ E F, E ⊆ I → F ⊆ I → Rulers.oE E ≤ Rulers.oE F → W F ≤ W E) ∧
      (∀ a b, a ⊆ I → b ⊆ I → b ⊂ a → W a - W b ≤ Houses.cHatH I k ℓ α a b) :=
  corollary_F' hI hℓ hα

-- Lemma N and Lemma F (F3), (F4)
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V')
    (hX : 0 < X1 I k ℓ α c (2 ^ #(I.erase c) - 1)) :
    IsPotential I k ℓ α (vPrime I k ℓ α c V') := lemma_N hI hℓ hα hne hc hV' hX
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') {f : ℕ}
    (hf : IsLeast {p | p < 2 ^ #(I.erase c) ∧ X1 I k ℓ α c p ≤ 0} f) (cF : ℤ)
    (hlo : loF I k ℓ α c V' f ≤ cF) (hhi : cF ≤ hiF I k ℓ α c V' f) :
    loF I k ℓ α c V' f ≤ hiF I k ℓ α c V' f ∧ IsPotential I k ℓ α (flatV I k ℓ α c V' f cF) :=
  ⟨(lemma_F hI hℓ hα hne hc hV' hf).2.2.1, (lemma_F hI hℓ hα hne hc hV' hf).2.2.2 cF hlo hhi⟩

-- Lemma P (P4): the junction bound
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    -X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ≤ ((k - c : ℕ) : ℤ) - α :=
  (lemma_P hI hℓ hα hne hc hV').2.2.2.2

#print axioms IsArrow.lt
#print axioms lemma_P1_low
#print axioms lemma_P1_high
#print axioms lemma_P1_cross
#print axioms lemma_P1_no_arrow
#print axioms lemma_P2
#print axioms lemma_P3
#print axioms lemma_P4
#print axioms lemma_P
#print axioms lemma_X
#print axioms lemma_N
#print axioms lemma_F1
#print axioms lemma_F2
#print axioms lemma_F3
#print axioms lemma_F4
#print axioms lemma_F
#print axioms theorem_F
#print axioms corollary_F'
