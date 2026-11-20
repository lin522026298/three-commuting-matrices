module

public import OriginAction
public import ActorIndex
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
noncomputable section
namespace DivisorG3
open Module LinearMap PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [Module (O k) W] [IsScalarTower k (O k) W]
def forgetEnd : End (O k) W →ₐ[k] End k W where
  toFun f := f.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl
abbrev triple (t y z : End k W) := Algebra.adjoin k ({t,y,z}:Set _)
abbrev pair (y z : End (O k) W) := Algebra.adjoin (O k) ({y,z}:Set _)
theorem exact_origin_actor (ρ : O k →ₐ[k] End k W) (T : End k W) (hX : ρ X=T)
    (hr : ρ.range=Algebra.adjoin k ({T}:Set _)) (hρ : ∀ s : O k, ∀ w : W, s • w=ρ s w)
    (y z : End (O k) W) :
    ((pair y z).restrictScalars k).map forgetEnd = triple T (y.restrictScalars k) (z.restrictScalars k) := by
  let D := triple T (y.restrictScalars k) (z.restrictScalars k)
  have ev (s : O k) : forgetEnd (algebraMap (O k) (End (O k) W) s)=ρ s := LinearMap.ext (hρ s)
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    change a ∈ Algebra.adjoin (O k) ({y,z}:Set _) at ha
    change forgetEnd a ∈ D
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_insert_iff.mp ha with h|h
      · subst a; exact Algebra.subset_adjoin (Or.inr (Or.inl rfl))
      · have h' := Set.mem_singleton_iff.mp h; subst a; exact Algebra.subset_adjoin (Or.inr (Or.inr rfl))
    | algebraMap s =>
      rw [ev]
      apply Algebra.adjoin_mono (s:=({T}:Set _)) (by rintro u rfl; exact Or.inl rfl)
      rw [←hr]; exact ⟨s,rfl⟩
    | add a b _ _ ha hb => exact D.add_mem ha hb
    | mul a b _ _ ha hb => exact D.mul_mem ha hb
  · apply Algebra.adjoin_le
    intro a ha
    rcases Set.mem_insert_iff.mp ha with h|h
    · subst a; exact ⟨_,(pair y z).algebraMap_mem X,(ev X).trans hX⟩
    · rcases Set.mem_insert_iff.mp h with h|h
      · subst a; exact ⟨y,Algebra.subset_adjoin (by simp),rfl⟩
      · have hh := Set.mem_singleton_iff.mp h; subst a; exact ⟨z,Algebra.subset_adjoin (by simp),rfl⟩

theorem origin_actor_length [FiniteDimensional k W] (ρ : O k →ₐ[k] End k W) (T : End k W) (hX : ρ X=T)
    (hr : ρ.range=Algebra.adjoin k ({T}:Set _)) (hρ : ∀ s : O k, ∀ w : W, s • w=ρ s w)
    (y z : End (O k) W) :
    length (O k) (pair y z) = finrank k (triple T (y.restrictScalars k) (z.restrictScalars k)) := by
  let A := (pair y z).restrictScalars k
  let D := triple T (y.restrictScalars k) (z.restrictScalars k)
  let f := Subalgebra.equivMapOfInjective A forgetEnd (fun _ _ h => LinearMap.ext fun w => congrArg (fun f : End k W => f w) h)
  have he : finrank k (pair y z)=finrank k D := by
    change finrank k A=finrank k (triple T (y.restrictScalars k) (z.restrictScalars k))
    rw [←exact_origin_actor ρ T hX hr hρ y z]
    exact f.toLinearEquiv.finrank_eq
  let e := f.toLinearMap
  let _ : Module.Finite k (pair y z) := Module.Finite.of_injective e f.injective
  exact (actual_length k (pair y z)).trans (congrArg Nat.cast he)
#print axioms exact_origin_actor
#print axioms origin_actor_length
end DivisorG3
