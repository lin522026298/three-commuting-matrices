module

public import Gerstenhaber.IdealQuotient.QuotientIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
The positive finite dual of a literal cyclic parent. The annihilator and
parent dimension are proved from the actual quotient action, without any
Gerstenhaber bound as an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.CanonicalExtension

open Module

variable {K A R0 : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing R0] [Algebra K R0]

abbrev canonicalParentModule (pi : A →ₐ[K] R0) : Module A (Module.Dual K R0) :=
  Gerstenhaber.IdealQuotient.dualModule
    ((Algebra.lsmul K K R0 : R0 →ₐ[K] Module.End K R0).comp pi)

theorem canonicalParent_tower (pi : A →ₐ[K] R0) :
    letI := canonicalParentModule pi
    IsScalarTower K A (Module.Dual K R0) :=
  Gerstenhaber.IdealQuotient.dualModule_tower _

theorem canonicalParent_annihilator (pi : A →ₐ[K] R0) :
    letI := canonicalParentModule pi
    Module.annihilator A (Module.Dual K R0) = RingHom.ker pi := by
  let := canonicalParentModule pi
  ext a
  rw [Module.mem_annihilator,RingHom.mem_ker]
  constructor
  · intro ha
    apply (Module.forall_dual_apply_eq_zero_iff K (pi a)).mp
    intro phi
    have h := LinearMap.congr_fun (ha phi) (1 : R0)
    change phi (pi a * 1) = 0 at h
    simpa only [mul_one] using h
  · intro ha phi
    ext r
    change phi (pi a * r) = 0
    rw [ha,zero_mul,map_zero]

/-- The parent action-image quotient and positive dual have equal
dimension because the given quotient homomorphism is genuinely onto. -/
theorem canonicalParent_dimension [FiniteDimensional K R0]
    (pi : A →ₐ[K] R0) (hpi : Function.Surjective pi) :
    letI := canonicalParentModule pi
    finrank K (A ⧸ Module.annihilator A (Module.Dual K R0)) =
      finrank K (Module.Dual K R0) := by
  let := canonicalParentModule pi
  rw [canonicalParent_annihilator,Subspace.dual_finrank_eq]
  exact (Ideal.quotientKerAlgEquivOfSurjective hpi).toLinearEquiv.finrank_eq

end Gerstenhaber.CanonicalExtension
