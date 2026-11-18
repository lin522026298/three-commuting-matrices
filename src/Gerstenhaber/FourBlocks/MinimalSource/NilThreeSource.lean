module

public import Gerstenhaber.FourBlocks.MinimalSource.ThreeGeneratorSafety

/-!
A finite nilpotent commuting triple with its literal generated algebra.
Commutativity, faithfulness, the three generators and augmentation are
proved for this actual image. No auxiliary algebra is substituted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap
open scoped IsMulCommutative

/-- A bundled finite source, with all carrier types in the field's
universe. This only bundles the literal hypotheses on a triple. -/
structure FiniteNilTriple (K : Type u) [Field K] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [module : Module K Carrier]
  [finiteDimensional : FiniteDimensional K Carrier]
  operator : Fin 3 → Module.End K Carrier
  commute : ∀ i j, Commute (operator i) (operator j)
  nilpotent : ∀ i, IsNilpotent (operator i)

attribute [instance] FiniteNilTriple.addCommGroup FiniteNilTriple.module
  FiniteNilTriple.finiteDimensional

variable {K : Type u} [Field K]

abbrev FiniteNilTriple.of (M : Type u) [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (X : Fin 3 → Module.End K M)
    (hcomm : ∀ i j, Commute (X i) (X j)) (hnil : ∀ i, IsNilpotent (X i)) :
    FiniteNilTriple K := ⟨M,X,hcomm,hnil⟩

def sourceAlgebra (X : FiniteNilTriple K) :
    Subalgebra K (Module.End K X.Carrier) :=
  Algebra.adjoin K (Set.range X.operator)

abbrev SourceAlgebra (X : FiniteNilTriple K) := sourceAlgebra X

instance sourceAlgebra_commutative (X : FiniteNilTriple K) :
    IsMulCommutative (SourceAlgebra X) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
  exact X.commute i j

instance sourceAlgebra_commRing (X : FiniteNilTriple K) : CommRing (SourceAlgebra X) :=
  inferInstance

instance sourceAlgebra_tower (X : FiniteNilTriple K) :
    IsScalarTower K (SourceAlgebra X) X.Carrier := ⟨fun _ _ _ => rfl⟩

instance sourceAlgebra_faithful (X : FiniteNilTriple K) :
    FaithfulSMul (SourceAlgebra X) X.Carrier :=
  ⟨fun h => Subtype.ext (LinearMap.ext h)⟩

def sourceRoot (X : FiniteNilTriple K) (i : Fin 3) : SourceAlgebra X :=
  ⟨X.operator i,Algebra.subset_adjoin ⟨i,rfl⟩⟩

@[simp] theorem sourceRoot_val (X : FiniteNilTriple K) (i : Fin 3) :
    (sourceRoot X i : Module.End K X.Carrier) = X.operator i := rfl

@[simp] theorem sourceRoot_lsmul (X : FiniteNilTriple K) (i : Fin 3) :
    Algebra.lsmul K K X.Carrier (sourceRoot X i) = X.operator i := rfl

theorem sourceRoot_nilpotent (X : FiniteNilTriple K) (i : Fin 3) :
    IsNilpotent (sourceRoot X i) := by
  exact (IsNilpotent.map_iff (f := (sourceAlgebra X).val) Subtype.val_injective).mp
    (X.nilpotent i)

theorem sourceRoot_adjoin_eq_top (X : FiniteNilTriple K) :
    Algebra.adjoin K (Set.range (sourceRoot X)) = ⊤ := by
  apply Subalgebra.map_injective (f := (sourceAlgebra X).val) Subtype.val_injective
  rw [AlgHom.map_adjoin,Algebra.map_top,Subalgebra.range_val]
  have hs : (sourceAlgebra X).val '' Set.range (sourceRoot X) =
      Set.range X.operator := by
    ext y
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨sourceRoot X i,⟨i,rfl⟩,rfl⟩
  rw [hs]
  rfl

theorem sourceActionImage_eq (X : FiniteNilTriple K) :
    actualActionImage (K := K) (A := SourceAlgebra X) (M := X.Carrier) = sourceAlgebra X := by
  ext f
  constructor
  · rintro ⟨a,rfl⟩
    exact a.property
  · intro hf
    exact ⟨⟨f,hf⟩,rfl⟩

theorem sourceAlgebra_finrank_le_square (X : FiniteNilTriple K) :
    finrank K (SourceAlgebra X) ≤ (finrank K X.Carrier)^2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (sourceAlgebra X).val.toLinearMap) Subtype.val_injective
  rw [Module.finrank_linearMap] at h
  simpa only [pow_two] using h

theorem sourceCarrier_nontrivial_of_failure (X : FiniteNilTriple K)
    (hbad : finrank K X.Carrier < finrank K (SourceAlgebra X)) : Nontrivial X.Carrier := by
  by_contra h
  let : Subsingleton X.Carrier := not_nontrivial_iff_subsingleton.mp h
  have hzero : finrank K X.Carrier = 0 := Module.finrank_zero_of_subsingleton
  have hle := sourceAlgebra_finrank_le_square X
  rw [hzero] at hbad hle
  omega

/-- This augmentation comes from the literal three nilpotent roots.
For a failed bound, its nontriviality requirement is proved above. -/
def sourceAugmentation (X : FiniteNilTriple K) [Nontrivial X.Carrier] :
    SourceAlgebra X →ₐ[K] K :=
  nilGeneratorAugmentation (sourceRoot X) (sourceRoot_nilpotent X)
    (sourceRoot_adjoin_eq_top X)

theorem sourceAugmentation_ker (X : FiniteNilTriple K) [Nontrivial X.Carrier] :
    augmentationIdeal (sourceAugmentation X) = Ideal.span (Set.range (sourceRoot X)) :=
  nilGeneratorAugmentation_ker _ _ _

theorem sourceAugmentation_nilpotent (X : FiniteNilTriple K) [Nontrivial X.Carrier] :
    IsNilpotent (augmentationIdeal (sourceAugmentation X)) :=
  nilGeneratorAugmentation_nilpotent _ _ _

@[simp] theorem sourceAugmentation_root (X : FiniteNilTriple K) [Nontrivial X.Carrier]
    (i : Fin 3) : sourceAugmentation X (sourceRoot X i) = 0 :=
  nilGeneratorAugmentation_root _ _ _ i

end Gerstenhaber.FourBlocks.MinimalSource
