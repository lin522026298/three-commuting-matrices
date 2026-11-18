module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Actual restrictions of a generated operator algebra. A spanning
family of invariant subspaces detects every original operator, so its
image algebra injects into the product of the actual restricted images. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Gerstenhaber.FourBlocks.PrimaryDecomposition

open Module LinearMap

variable {K V ι η : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev Generated (T : ι → Module.End K V) := Algebra.adjoin K (Set.range T)

def root (T : ι → Module.End K V) (i : ι) : Generated T :=
  ⟨T i,Algebra.subset_adjoin ⟨i,rfl⟩⟩

theorem root_adjoin (T : ι → Module.End K V) :
    Algebra.adjoin K (Set.range (root T))=⊤ := by
  apply Subalgebra.map_injective (f := (Generated T).val) Subtype.val_injective
  rw [AlgHom.map_adjoin,Algebra.map_top,Subalgebra.range_val]
  have hs : (Generated T).val '' Set.range (root T)=Set.range T := by
    ext f
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨root T i,⟨i,rfl⟩,rfl⟩
  rw [hs]

theorem adjoin_mapsTo (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (a : Generated T) :
    Set.MapsTo (a : Module.End K V) P P := by
  have hs : ∀ f ∈ Algebra.adjoin K (Set.range T), Set.MapsTo f P P := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨i,rfl⟩ := hf
      exact hP i
    | algebraMap k =>
      intro x hx
      exact P.smul_mem k hx
    | add f g _ _ hf hg =>
      intro x hx
      exact P.add_mem (hf hx) (hg hx)
    | mul f g _ _ hf hg =>
      intro x hx
      exact hf (hg hx)
  exact hs a a.property

def restrictionHom (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) : Generated T →ₐ[K] Module.End K P where
  toFun a := (a : Module.End K V).restrict (adjoin_mapsTo T P hP a)
  map_zero' := by ext x; rfl
  map_one' := by ext x; rfl
  map_add' a b := by ext x; rfl
  map_mul' a b := by ext x; rfl
  commutes' k := by ext x; rfl

def restricted (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) : ι → Module.End K P :=
  fun i => (T i).restrict (hP i)

@[simp] theorem restrictionHom_root (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (i : ι) :
    restrictionHom T P hP (root T i)=restricted T P hP i := rfl

@[simp] theorem restricted_coe (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (i : ι) (x : P) :
    (restricted T P hP i x : V)=T i x := rfl

theorem restrictionHom_range (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) :
    (restrictionHom T P hP).range=Generated (restricted T P hP) := by
  have h := AlgHom.map_adjoin (restrictionHom T P hP) (Set.range (root T))
  rw [root_adjoin,Algebra.map_top] at h
  have hs : restrictionHom T P hP '' Set.range (root T)=Set.range (restricted T P hP) := by
    ext f
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨root T i,⟨i,rfl⟩,rfl⟩
  rw [hs] at h
  exact h

def allRestrictions (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) :
    Generated T →ₗ[K] ∀ i, (restrictionHom T (P i) (hP i)).range :=
  LinearMap.pi fun i => (restrictionHom T (P i) (hP i)).rangeRestrict.toLinearMap

theorem allRestrictions_injective (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) (hspan : ⨆ i, P i=⊤) :
    Function.Injective (allRestrictions T P hP) := by
  intro a b hab
  apply Subtype.ext
  let f : Module.End K V := (a : Module.End K V)-(b : Module.End K V)
  have hle : ⨆ i, P i ≤ f.ker := by
    apply iSup_le
    intro i x hx
    have h := congrArg (fun z => ((z i : Module.End K (P i)) ⟨x,hx⟩ : V)) hab
    change (a : Module.End K V) x=(b : Module.End K V) x at h
    exact sub_eq_zero.mpr h
  rw [hspan] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule K V) from trivial)
  exact sub_eq_zero.mp hx

theorem generated_finrank_le_sum [Fintype η] [FiniteDimensional K V]
    (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) (hspan : ⨆ i, P i=⊤)
    (hbound : ∀ i, finrank K (Generated (restricted T (P i) (hP i))) ≤ finrank K (P i)) :
    finrank K (Generated T) ≤ ∑ i, finrank K (P i) := by
  have : ∀ i, Module.Free K (restrictionHom T (P i) (hP i)).range :=
    fun i => Module.Free.of_divisionRing K (restrictionHom T (P i) (hP i)).range
  have : ∀ i, Module.Finite K (restrictionHom T (P i) (hP i)).range := fun i => inferInstance
  have h := LinearMap.finrank_le_finrank_of_injective (allRestrictions_injective T P hP hspan)
  rw [Module.finrank_pi_fintype] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  rw [restrictionHom_range]
  exact hbound i

def shifted (T : ι → Module.End K V) (chi : ι → K) : ι → Module.End K V :=
  fun i => T i-chi i • 1

theorem adjoin_shifted (T : ι → Module.End K V) (chi : ι → K) :
    Generated (shifted T chi)=Generated T := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro f ⟨i,rfl⟩
    exact (Generated T).sub_mem (Algebra.subset_adjoin ⟨i,rfl⟩)
      ((Generated T).algebraMap_mem (chi i))
  · apply Algebra.adjoin_le
    rintro f ⟨i,rfl⟩
    have h1 : shifted T chi i ∈ Generated (shifted T chi) := Algebra.subset_adjoin ⟨i,rfl⟩
    have h2 : (chi i • (1 : Module.End K V)) ∈ Generated (shifted T chi) :=
      (Generated (shifted T chi)).algebraMap_mem (chi i)
    simpa only [shifted,sub_add_cancel,SetLike.mem_coe] using (Generated (shifted T chi)).add_mem h1 h2

end Gerstenhaber.FourBlocks.PrimaryDecomposition
