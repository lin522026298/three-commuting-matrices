module

public import Gerstenhaber.CanonicalExtension.KernelDuality
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Positive duality for the actual given commutative-algebra action.
Exactness, faithfulness and compatibility with literal quotient actions
are proved, rather than inferred from vector-space dimensions. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.CanonicalExtension

open Module

variable {K A M N Q : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]

abbrev positiveDualModule : Module A (Module.Dual K M) :=
  Gerstenhaber.IdealQuotient.dualModule (Algebra.lsmul K K M)

theorem positiveDual_tower :
    letI := positiveDualModule (K := K) (A := A) (M := M)
    IsScalarTower K A (Module.Dual K M) :=
  Gerstenhaber.IdealQuotient.dualModule_tower _

def positiveDualMap (f : M →ₗ[A] N) :
    letI := positiveDualModule (K := K) (A := A) (M := N)
    letI := positiveDualModule (K := K) (A := A) (M := M)
    Module.Dual K N →ₗ[A] Module.Dual K M := by
  let := positiveDualModule (K := K) (A := A) (M := N)
  let := positiveDualModule (K := K) (A := A) (M := M)
  exact
    { toFun := (f.restrictScalars K).dualMap
      map_add' := (f.restrictScalars K).dualMap.map_add
      map_smul' := by
        intro a phi
        ext x
        change phi (a • f x) = phi (f (a • x))
        rw [f.map_smul] }

@[simp] theorem positiveDualMap_apply (f : M →ₗ[A] N)
    (phi : Module.Dual K N) (x : M) : positiveDualMap (K := K) f phi x = phi (f x) := rfl

theorem positiveDualMap_injective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Injective (positiveDualMap (K := K) f) :=
  LinearMap.dualMap_injective_of_surjective hf

theorem positiveDualMap_surjective (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Surjective (positiveDualMap (K := K) f) :=
  LinearMap.dualMap_surjective_of_injective hf

theorem positiveDualMap_exact (i : N →ₗ[A] M) (p : M →ₗ[A] Q)
    (hexact : i.range = p.ker) :
    letI := positiveDualModule (K := K) (A := A) (M := Q)
    letI := positiveDualModule (K := K) (A := A) (M := M)
    letI := positiveDualModule (K := K) (A := A) (M := N)
    (positiveDualMap (K := K) p).range = (positiveDualMap (K := K) i).ker := by
  let := positiveDualModule (K := K) (A := A) (M := Q)
  let := positiveDualModule (K := K) (A := A) (M := M)
  let := positiveDualModule (K := K) (A := A) (M := N)
  have hexK : (i.restrictScalars K).range = (p.restrictScalars K).ker := by
    ext x
    exact SetLike.ext_iff.mp hexact x
  have h : ((p.restrictScalars K).dualMap).range = ((i.restrictScalars K).dualMap).ker := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range,hexK]
  ext phi
  exact SetLike.ext_iff.mp h phi

theorem positiveDual_annihilator :
    letI := positiveDualModule (K := K) (A := A) (M := M)
    Module.annihilator A (Module.Dual K M) = Module.annihilator A M := by
  let := positiveDualModule (K := K) (A := A) (M := M)
  ext a
  rw [Module.mem_annihilator,Module.mem_annihilator]
  constructor
  · intro ha x
    apply (Module.forall_dual_apply_eq_zero_iff K (a • x)).mp
    intro phi
    exact LinearMap.congr_fun (ha phi) x
  · intro ha phi
    ext x
    change phi (a • x) = 0
    rw [ha,map_zero]

theorem positiveDual_faithful [FaithfulSMul A M] :
    letI := positiveDualModule (K := K) (A := A) (M := M)
    FaithfulSMul A (Module.Dual K M) := by
  let := positiveDualModule (K := K) (A := A) (M := M)
  apply Module.annihilator_eq_bot.mp
  rw [positiveDual_annihilator]
  exact Module.annihilator_eq_bot.mpr inferInstance

section Quotient

variable {B : Type*} [CommRing B] [Algebra K B]

theorem positiveDual_quotient_action (pi : A →ₐ[K] B) :
    letI := quotientKernelModule pi
    positiveDualModule (K := K) (A := A) (M := B) = canonicalParentModule pi := rfl

end Quotient

end Gerstenhaber.CanonicalExtension
