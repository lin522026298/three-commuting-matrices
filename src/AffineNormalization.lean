module

public import PolePrime
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.FieldTheory.SeparableDegree

@[expose] public section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
namespace GKDivisor

open scoped nonZeroDivisors
attribute [local instance] FractionRing.liftAlgebra

/-- Finiteness of affine normalisation in characteristic zero: Noether normalization and the
trace-dual bound for the integral closure in a finite separable field extension. -/
theorem finite_affine_normalization (k R : Type*) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨n, f, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let S := MvPolynomial (Fin n) k
  let K := FractionRing S
  let L := FractionRing R
  let B := integralClosure R L
  letI : Algebra S R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hinj
  haveI : Module.Finite S R := hfin
  haveI : IsScalarTower S R L := inferInstance
  haveI : FaithfulSMul S L := inferInstance
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : FiniteDimensional K L := Module.Finite.of_isLocalization S R S⁰
  letI : Algebra S B := ((algebraMap R B).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower S R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral S B := Algebra.IsIntegral.trans R
  haveI : IsIntegrallyClosedIn B L := IsIntegrallyClosedIn.of_isIntegralClosure R
  haveI : IsIntegralClosure B S L := IsIntegralClosure.of_isIntegrallyClosedIn
  haveI : Module.Finite S B := IsIntegralClosure.finite S K L B
  exact Module.Finite.of_restrictScalars_finite S R B

/-- For any affine domain of characteristic zero a nonzero nonunit defines a DVR on the
finite normalization. Its center really contains the original element. -/
theorem affine_nonunit_divisor (k R : Type*) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    let N := integralClosure R (FractionRing R)
    ∃ P : Ideal N, ∃ hp : P.IsPrime, algebraMap R N q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime N _ P hp) := by
  let N := integralClosure R (FractionRing R)
  haveI : Module.Finite R N := finite_affine_normalization k R
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : IsNoetherianRing N := IsNoetherianRing.of_finite R N
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hI : Function.Injective (algebraMap R N) := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  haveI : FaithfulSMul R N := (faithfulSMul_iff_algebraMap_injective R N).mpr hI
  apply nonunit_divisor (algebraMap R N q) ((map_ne_zero_iff _ hI).mpr hq)
  exact fun h => hn (isUnit_of_map_unit (algebraMap R N) q h)

#print axioms GKDivisor.finite_affine_normalization
#print axioms GKDivisor.affine_nonunit_divisor
end GKDivisor
