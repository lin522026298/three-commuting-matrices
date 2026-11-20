module

public import GKGraphIntegral
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace GKGraph
universe u
variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_adjoin_family {ι : Type} [Fintype ι] (x : ι → F) :
    Algebra.trdeg k (IntermediateField.adjoin k (Set.range x)) ≤ (Fintype.card ι : ℕ) := by
  let S := Set.range x
  have hi : Algebra.IsAlgebraic (Algebra.adjoin k S) (IntermediateField.adjoin k S) := inferInstance
  change Algebra.trdeg k (IntermediateField.adjoin k S) ≤ _
  rw [← trdeg_add_eq k (Algebra.adjoin k S) (A := IntermediateField.adjoin k S),
      trdeg_eq_zero_iff.2 hi, add_zero]
  dsimp only [S]
  rw [Algebra.adjoin_range_eq_range_aeval]
  let f := (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] F)
  have hf : Function.Surjective f.rangeRestrict := by rintro ⟨_,y,rfl⟩; exact ⟨y,rfl⟩
  have h := trdeg_le_of_surjective f.rangeRestrict hf
  simpa [MvPolynomial.trdeg_of_isDomain] using h

variable (r : ℕ) (φ : ring k r →ₐ[k] F)
def residueCoordinates := IntermediateField.adjoin k (Set.range (φ ∘ gcoord k r))
def reducedMatrices (i : Fin 6) := φ.mapMatrix (gmat k r i)
theorem reduced_entry (l : Fin 6) (i j : Fin r) :
    reducedMatrices k r φ l i j = φ (gcoord k r (l,i,j)) := rfl

theorem residueCoordinates_eq :
    residueCoordinates k r φ = IntermediateField.adjoin k (Set.range φ) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩; exact IntermediateField.subset_adjoin _ _ ⟨_,rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x,rfl⟩
    have hl : φ x ∈ φ.range := ⟨x,rfl⟩
    rw [range_generated] at hl
    exact IntermediateField.algebra_adjoin_le_adjoin k _ hl

def pairField {n : ℕ} (center : Fin 2 → F) (u : Fin n → F) :=
  IntermediateField.adjoin k (Set.range (Sum.elim center u))

/-- The two spectral shifts are counted only once. The two pairs can have completely
different orbit/centralizer parameters; none are presumed algebraically independent. -/
theorem joint_coordinate_budget {s t : ℕ} (center : Fin 2 → F)
    (u : Fin s → F) (v : Fin t → F)
    (h0 : reducedMatrices k r φ 0 = 0)
    (h1 : ∀ i j, reducedMatrices k r φ 1 i j ∈ pairField k center u)
    (h2 : ∀ i j, reducedMatrices k r φ 2 i j ∈ pairField k center u)
    (h3 : ∀ i j, reducedMatrices k r φ 3 i j ∈ pairField k center v)
    (h4 : ∀ i j, reducedMatrices k r φ 4 i j ∈ pairField k center v) :
    Algebra.trdeg k (residueCoordinates k r φ) ≤ (2 + s + t + r*r : ℕ) := by
  let q := fun z : Fin r × Fin r => reducedMatrices k r φ 5 z.1 z.2
  let w := Sum.elim center (Sum.elim u (Sum.elim v q))
  let E := IntermediateField.adjoin k (Set.range w)
  have hw : ∀ j, w j ∈ E := fun j => IntermediateField.subset_adjoin _ _ ⟨j,rfl⟩
  have hu : pairField k center u ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact hw (.inl i)
    | inr i => exact hw (.inr (.inl i))
  have hv : pairField k center v ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact hw (.inl i)
    | inr i => exact hw (.inr (.inr (.inl i)))
  have he : residueCoordinates k r φ ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨p,i,j⟩,rfl⟩
    change reducedMatrices k r φ p i j ∈ E
    fin_cases p
    · exact (congrFun (congrFun h0 i) j).symm ▸ E.zero_mem
    · exact hu (h1 _ _)
    · exact hu (h2 _ _)
    · exact hv (h3 _ _)
    · exact hv (h4 _ _)
    · exact hw (.inr (.inr (.inr (i,j))))
  refine (trdeg_le_of_injective (IntermediateField.inclusion he)
    (IntermediateField.inclusion he).injective).trans ?_
  simpa [E,w,Fintype.card_sum,Fintype.card_prod,Nat.add_assoc] using trdeg_adjoin_family k w

theorem joint_coordinate_bound (hr : 2 ≤ r) (center : Fin 2 → F)
    (u v : Fin (r*r-2) → F)
    (h0 : reducedMatrices k r φ 0 = 0)
    (h1 : ∀ i j, reducedMatrices k r φ 1 i j ∈ pairField k center u)
    (h2 : ∀ i j, reducedMatrices k r φ 2 i j ∈ pairField k center u)
    (h3 : ∀ i j, reducedMatrices k r φ 3 i j ∈ pairField k center v)
    (h4 : ∀ i j, reducedMatrices k r φ 4 i j ∈ pairField k center v) :
    Algebra.trdeg k (residueCoordinates k r φ) ≤ (3*r*r-2 : ℕ) := by
  have hrr : 2 ≤ r*r := (by omega : 2 ≤ 2*2).trans (Nat.mul_le_mul hr hr)
  have e : 2 + (r*r-2) + (r*r-2) + r*r = 3*r*r-2 := by rw [Nat.mul_assoc]; omega
  rw [←e]
  exact joint_coordinate_budget k r φ center u v h0 h1 h2 h3 h4
end GKGraph
