module

public import Gerstenhaber.CanonicalExtension.ParentDuality
public import Gerstenhaber.CanonicalExtension.FrobeniusIsotropy

/-! The kernel Frobenius identification is an equivalence for the ACTUAL
quotient action, not an abstract vector-space isomorphism. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.CanonicalExtension

open Gerstenhaber.DP2.LinearRow

variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]

abbrev quotientKernelModule (pi : A →ₐ[K] B) : Module A B :=
  Module.compHom B pi.toRingHom

theorem quotientKernel_tower (pi : A →ₐ[K] B) :
    letI := quotientKernelModule pi
    IsScalarTower K A B := by
  let := quotientKernelModule pi
  refine ⟨?_⟩
  intro k a b
  change pi (k • a)*b = k • (pi a*b)
  have h : pi (k • a) = k • pi a := map_smul pi k a
  rw [h,Algebra.smul_mul_assoc]

def kernelFrobeniusMap (pi : A →ₐ[K] B) (tau : B →ₗ[K] K) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    B →ₗ[A] Module.Dual K B := by
  let := quotientKernelModule pi
  let := canonicalParentModule pi
  exact
    { toFun := frobeniusPairing tau
      map_add' := (frobeniusPairing tau).map_add
      map_smul' := by
        intro a b
        ext c
        change tau ((pi a*b)*c) = tau (b*(pi a*c))
        simp only [mul_assoc,mul_left_comm] }

theorem kernelFrobeniusMap_bijective (pi : A →ₐ[K] B) (tau : B →ₗ[K] K)
    (htau : Function.Bijective (frobeniusPairing tau)) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    Function.Bijective (kernelFrobeniusMap pi tau) := by
  exact htau

def kernelFrobeniusEquiv (pi : A →ₐ[K] B) (tau : B →ₗ[K] K)
    (htau : Function.Bijective (frobeniusPairing tau)) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    B ≃ₗ[A] Module.Dual K B := by
  let := quotientKernelModule pi
  let := canonicalParentModule pi
  exact LinearEquiv.ofBijective (kernelFrobeniusMap pi tau)
    (kernelFrobeniusMap_bijective pi tau htau)

end Gerstenhaber.CanonicalExtension
