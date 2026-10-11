import RequestProject.TheoremF.All

/-! Auditor's check file for Lean piece C7 (Grepy Escribano, 6 Oct 2026).
Encodings written out by hand from `C7_theorem_F_walk_and_cut.md` and closed by `rfl`; the main
statements restated by hand and closed by the certified theorems; then `#print axioms`. -/

open TheoremF Finset AntitonicFit

-- Encodings (Setting of the file)
example (I : Finset ℕ) (p : ℕ) :
    dancer I p = I.filter (fun t => Houses.bit (#(I.filter (· < t))) p = 1) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (p : ℕ) :
    xHseq I k ℓ α p = Houses.xH I k ℓ α (dancer I p) := rfl
example (I : Finset ℕ) (k ℓ p : ℕ) : JHseq I k ℓ p = Houses.JH k ℓ (dancer I p) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c p : ℕ) :
    dWalk I k ℓ α c p = Houses.d1 I k ℓ α c (dancer (I.erase c) p) := rfl

-- Lemma 0
example (I : Finset ℕ) (p : ℕ) : dancer I p ⊆ I := lemma_0a I p
example (I : Finset ℕ) {p q : ℕ} (hpq : p < q) (hq : q < 2 ^ #I) :
    Rulers.oE (dancer I p) < Rulers.oE (dancer I q) := lemma_0b hpq hq
example (I : Finset ℕ) {D : Finset ℕ} (hD : D ⊆ I) : ∃! p, p < 2 ^ #I ∧ dancer I p = D :=
  lemma_0c_existsUnique hD
example (I : Finset ℕ) {p : ℕ} (hp : p < 2 ^ #I) : GoldenMatching.rank I (dancer I p) = p :=
  lemma_0c_rank hp
example (I : Finset ℕ) {p : ℕ} (hp : p < 2 ^ #I) : dancer I (2 ^ #I - 1 - p) = I \ dancer I p :=
  lemma_0d hp
example (I : Finset ℕ) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) {p : ℕ}
    (hp : p < 2 ^ #(I.erase c)) :
    dancer I p = dancer (I.erase c) p ∧
      dancer I (2 ^ #(I.erase c) + p) = dancer (I.erase c) p ∪ {c} := lemma_0e hne hc hp

-- Lemma 0f
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) {p : ℕ} (hp : p < 2 ^ #I) :
    xHseq I k ℓ α (2 ^ #I - 1 - p) = -xHseq I k ℓ α p := lemma_0f_antisymm I k ℓ α p hp
example (I : Finset ℕ) {k ℓ : ℕ} (hℓ : ℓ < 2 ^ k) : JHseq I k ℓ 0 = 0 := lemma_0f_J0 I hℓ

-- Theorem F1: (Λ) and the strict (Cut) at b and at N − b
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∀ p < 2 ^ #I, |ifit (2 ^ #I) (fun q => Houses.xH I k ℓ α (dancer I q)) p| ≤ α * (2 ^ k - 1) :=
  theorem_F1_Lambda hI hℓ hα
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α)
    (b : ℕ) (hb : b < 2 ^ #I) (hJb : Houses.JH k ℓ (dancer I b) = 1)
    (hfirst : ∀ p < b, Houses.JH k ℓ (dancer I p) = 0) :
    IsStrictCut (2 ^ #I) (toR (fun q => Houses.xH I k ℓ α (dancer I q))) b ∧
      IsStrictCut (2 ^ #I) (toR (fun q => Houses.xH I k ℓ α (dancer I q))) (2 ^ #I - b) :=
  theorem_F1_Cut hI hℓ hα b hb hJb hfirst

-- Theorem F0: (W0), (W1), (W2)
example {I : Finset ℕ} {k ℓ : ℕ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ)
    (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) (p : ℕ) (hp : p < 2 ^ #(I.erase c)) :
    Houses.xH I k ℓ α (dancer I p) =
      Houses.xH (I.erase c) c (ℓ % 2 ^ c) α (dancer (I.erase c) p) +
        Houses.d1 I k ℓ α c (dancer (I.erase c) p) :=
  theorem_F0_W0 hI hℓ α hne hc p hp
example {I : Finset ℕ} {k ℓ : ℕ} (α : ℤ) (c p : ℕ) (hp : p + 1 < 2 ^ #(I.erase c)) :
    dWalk I k ℓ α c (p + 1) ≤ dWalk I k ℓ α c p := theorem_F0_W1_antitone α c p hp
example {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) (p : ℕ) (hp : p < 2 ^ #(I.erase c)) :
    ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c) p =
      ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) p + dWalk I k ℓ α c p :=
  (theorem_F0_W2 (k := k) hα hne hc).2 p hp

#print axioms lemma_0a
#print axioms lemma_0b
#print axioms lemma_0c_existsUnique
#print axioms lemma_0c_rank
#print axioms lemma_0d
#print axioms lemma_0e
#print axioms lemma_0f_antisymm
#print axioms lemma_0f_J0
#print axioms theorem_F1
#print axioms theorem_F1_Lambda
#print axioms theorem_F1_Cut
#print axioms theorem_F0
#print axioms theorem_F0_W0
#print axioms theorem_F0_W1_antitone
#print axioms theorem_F0_W1_change
#print axioms theorem_F0_W2
#print axioms theorem_F0_W3
