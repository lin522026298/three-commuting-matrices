module

public import Gerstenhaber.FourBlocks.MinimalSource.NilpotentResidue
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Actual annihilator fibers and the restricted-minimum budget.  The safety
inputs concern the actual image algebras on the specified shorter
submodules and quotients.  They are not socle-injectivity, fiber-equality,
or numerical type-budget assumptions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

abbrev actualActionImage := (Algebra.lsmul K K M : A →ₐ[K] Module.End K M).range

theorem actualActionImage_finrank :
    finrank K (actualActionImage (K := K) (A := A) (M := M)) =
      finrank K (A ⧸ Module.annihilator A M) := by
  have hker : RingHom.ker (Algebra.lsmul K K M : A →ₐ[K] Module.End K M) =
      Module.annihilator A M := by
    ext a
    rw [RingHom.mem_ker,Module.mem_annihilator]
    constructor
    · intro h x
      exact LinearMap.congr_fun h x
    · intro h
      exact LinearMap.ext h
  rw [← hker]
  exact (Ideal.quotientKerEquivRange
    (Algebra.lsmul K K M : A →ₐ[K] Module.End K M)).toLinearEquiv.finrank_eq.symm

theorem algebraSocle_finrank_le_product [FiniteDimensional K M] [FaithfulSMul A M]
    (eps : A →ₐ[K] K) :
    finrank K (algebraSocle eps) ≤
      finrank K (Top (M := M) eps)*finrank K (moduleSocle (M := M) eps) := by
  let : FiniteDimensional K (Top (M := M) eps) :=
    FiniteDimensional.of_surjective (topProjection eps) (topProjection_surjective eps)
  let : FiniteDimensional K (moduleSocle (M := M) eps) :=
    FiniteDimensional.of_injective ((moduleSocle eps).subtype.restrictScalars K)
      (moduleSocle eps).injective_subtype
  have h := LinearMap.finrank_le_finrank_of_injective (socleAction_injective (M := M) eps)
  rw [Module.finrank_linearMap] at h
  exact h

/-- Full socle action at the numerical equality boundary is proved
from the same actual injection, rather than taken as an extra source
hypothesis. -/
theorem socleAction_bijective_of_finrank_eq [FiniteDimensional K A]
    [FiniteDimensional K M] [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (hdim : finrank K (algebraSocle eps) =
      finrank K (Top (M := M) eps)*finrank K (moduleSocle (M := M) eps)) :
    Function.Bijective (socleAction (M := M) eps) := by
  let : FiniteDimensional K (Top (M := M) eps) :=
    FiniteDimensional.of_surjective (topProjection eps) (topProjection_surjective eps)
  let : FiniteDimensional K (moduleSocle (M := M) eps) :=
    FiniteDimensional.of_injective ((moduleSocle eps).subtype.restrictScalars K)
      (moduleSocle eps).injective_subtype
  have heq : finrank K (algebraSocle eps) =
      finrank K (Top (M := M) eps →ₗ[K] moduleSocle (M := M) eps) := by
    rw [Module.finrank_linearMap]
    exact hdim
  exact ⟨socleAction_injective eps,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp (socleAction_injective eps)⟩

/-- The actual source budget after applying safety only to its
codimension-one top kernels and its socle-line quotients.  Nilpotence
of the literal augmentation ideal supplies nonzero top and socle. -/
theorem actual_socle_budget_of_shorter_safety [Infinite K]
    [FiniteDimensional K A] [FiniteDimensional K M] [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (e : ℕ)
    (hdim : finrank K A=finrank K M+e)
    (hnil : IsNilpotent (augmentationIdeal eps))
    (hsub : ∀ (φ : Module.Dual K (Top (M := M) eps)), φ ≠ 0 →
      finrank K (actualActionImage (K := K) (A := A) (M := topHyperplane eps φ)) ≤
        finrank K (topHyperplane eps φ))
    (hquot : ∀ (v : moduleSocle (M := M) eps), v ≠ 0 →
      finrank K (actualActionImage (K := K) (A := A) (M := M ⧸ socleLine eps v)) ≤
        finrank K (M ⧸ socleLine eps v)) :
    e+1 ≤ finrank K (Top (M := M) eps) ∧
      e+1 ≤ finrank K (moduleSocle (M := M) eps) ∧
      (e+1)*(finrank K (Top (M := M) eps)+finrank K (moduleSocle (M := M) eps)-(e+1)) ≤
        finrank K (algebraSocle eps) := by
  let : Nontrivial M := faithful_module_nontrivial eps
  let : Nontrivial (Top (M := M) eps) := top_nontrivial_of_nilpotent eps hnil
  let : Nontrivial (moduleSocle (M := M) eps) := socle_nontrivial_of_nilpotent eps hnil
  let : FiniteDimensional K (Top (M := M) eps) :=
    FiniteDimensional.of_surjective (topProjection eps) (topProjection_surjective eps)
  let : FiniteDimensional K (moduleSocle (M := M) eps) :=
    FiniteDimensional.of_injective ((moduleSocle eps).subtype.restrictScalars K)
      (moduleSocle eps).injective_subtype
  have hfunctional (φ : Module.Dual K (Top (M := M) eps)) (hφ : φ ≠ 0) :
      e+1 ≤ finrank K (fixedFunctionalFiber (socleTensor eps) φ) := by
    have hshort := hsub φ hφ
    rw [actualActionImage_finrank] at hshort
    have hlen := topHyperplane_finrank_add_one eps φ hφ
    have hadd := ((Module.annihilator A (topHyperplane eps φ)).restrictScalars K).finrank_quotient_add_finrank
    change finrank K (A ⧸ Module.annihilator A (topHyperplane eps φ))+
      finrank K (Module.annihilator A (topHyperplane eps φ)) = finrank K A at hadd
    have hfiber := (hyperplaneAnnFiberEquiv eps φ hφ).finrank_eq
    omega
  have hvector (v : moduleSocle (M := M) eps) (hv : v ≠ 0) :
      e+1 ≤ finrank K (fixedVectorFiber (socleTensor eps) v) := by
    have hshort := hquot v hv
    rw [actualActionImage_finrank] at hshort
    have hlen := socleLine_quotient_finrank_add_one eps v hv
    have hadd := ((Module.annihilator A (M ⧸ socleLine eps v)).restrictScalars K).finrank_quotient_add_finrank
    change finrank K (A ⧸ Module.annihilator A (M ⧸ socleLine eps v))+
      finrank K (Module.annihilator A (M ⧸ socleLine eps v)) = finrank K A at hadd
    have hfiber := (lineQuotientAnnFiberEquiv eps v hv).finrank_eq
    omega
  have h := socle_tensor_nonzero_fiber_budget (socleTensor eps) (e+1) hfunctional hvector
  rw [socleTensor_finrank] at h
  exact h

end Gerstenhaber.FourBlocks.MinimalSource
