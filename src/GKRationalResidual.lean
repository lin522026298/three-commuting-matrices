module

public import GKRationalAdjunction
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section
namespace GKRational
variable {A K B : Type*} [CommRing A] [Field K] [Algebra A K] [CommRing B]
variable (a b : A)

/-- This holds even for an arbitrary polynomial/rational singleton adjunction:
once its adjoined element dies, no extra residual coordinates remain. -/
theorem range_eq_base_of_q_zero (ψ : adj (K := K) a b →+* B)
    (hq : ψ (q a b) = 0) : ψ.range = (ψ.comp (algebraMap A (adj a b))).range := by
  apply le_antisymm _ (by rintro _ ⟨x,rfl⟩; exact ⟨_,rfl⟩)
  rintro _ ⟨x,rfl⟩
  let T : Subalgebra A (adj (K := K) a b) :=
    { (ψ.comp (algebraMap A (adj a b))).range.comap ψ with
      algebraMap_mem' := fun y => ⟨y,rfl⟩ }
  have hq' : q a b ∈ T := ⟨0, by rw [map_zero,hq]⟩
  have ht : Algebra.adjoin A ({q a b} : Set (adj (K := K) a b)) = ⊤ := by
    apply Subalgebra.map_injective (f := (adj a b).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
    rfl
  have hh : ⊤ ≤ T := by rw [←ht]; exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hq')
  exact hh (show x ∈ (⊤ : Subalgebra A _) from Algebra.mem_top)

theorem residue_surjective (P : Ideal (adj (K := K) a b)) (hq : q a b ∈ P) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap A (adj a b))) := by
  intro x
  have H : x ∈ (Ideal.Quotient.mk P).range := Ideal.Quotient.mk_surjective x
  rw [range_eq_base_of_q_zero a b _ (Ideal.Quotient.eq_zero_iff_mem.mpr hq)] at H
  exact H

theorem residual_representative (P : Ideal (adj (K := K) a b)) (hq : q a b ∈ P) (z : adj a b) :
    ∃ x : A, z - algebraMap A (adj a b) x ∈ P := by
  obtain ⟨x,hx⟩ := residue_surjective a b P hq (Ideal.Quotient.mk P z)
  exact ⟨x,Ideal.Quotient.eq.mp hx.symm⟩

end GKRational
