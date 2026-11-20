module

public import PolePrime
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import GKFiniteFrobenius

@[expose] public section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
noncomputable section
namespace GKDivisor

open scoped nonZeroDivisors
attribute [local instance] FractionRing.liftAlgebra

private theorem finite_left_of_injective {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    (f : A →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  algebraize [f, g, g.comp f]
  exact Module.Finite.of_injective ((Algebra.linearMap B C).restrictScalars A) hg

/-- A uniform Frobenius power embeds the integral closure into the
integral closure in the separable subextension. On scalars this embedding
acts by a finite endomorphism. -/
private theorem finite_integralClosure_over_polynomial (k S K L : Type*)
    [Field k] [PerfectField k] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsNoetherianRing S] [Algebra k S] [Algebra.FiniteType k S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L]
    [Algebra S L] [Algebra K L] [IsScalarTower S K L] [FiniteDimensional K L] :
    Module.Finite S (integralClosure S L) := by
  let T := separableClosure K L
  letI : Algebra S T := ((algebraMap K T).comp (algebraMap S K)).toAlgebra
  haveI : IsScalarTower S K T := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S T L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply S K L x
  haveI : FiniteDimensional K T := inferInstanceAs (FiniteDimensional K (separableClosure K L))
  haveI : Algebra.IsSeparable K T := inferInstanceAs (Algebra.IsSeparable K (separableClosure K L))
  haveI : IsPurelyInseparable T L := inferInstanceAs (IsPurelyInseparable (separableClosure K L) L)
  haveI : FiniteDimensional T L := Module.Finite.of_restrictScalars_finite K T L
  let D := integralClosure S L
  let C := integralClosure S T
  haveI : Module.Finite S C := IsIntegralClosure.finite S K T C
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar S p := expChar_of_injective_algebraMap (algebraMap k S).injective p
  haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective S K) p
  haveI : ExpChar T p := expChar_of_injective_algebraMap (algebraMap K T).injective p
  haveI : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  let e := IsPurelyInseparable.exponent T L
  have hpow (x : L) : x ^ p ^ e ∈ T := by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' T p x
    rw [← hy]
    exact y.property
  let ψ : L →+* T := (iterateFrobenius L p e).codRestrict T.toSubfield.toSubring hpow
  let g : D →+* C := (ψ.comp D.val.toRingHom).codRestrict C.toSubring fun x ↦ by
    change IsIntegral S (ψ x.val)
    apply (isIntegral_algebraMap_iff (B := L)).mp
    exact x.property.pow _
  have heq : g.comp (algebraMap S D) = (algebraMap S C).comp (iterateFrobenius S p e) := by
    ext x
    change (algebraMap S L x) ^ p ^ e = algebraMap T L (algebraMap S T (x ^ p ^ e))
    rw [← IsScalarTower.algebraMap_apply, map_pow]
  have hg : Function.Injective g := by
    intro a b h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  apply (RingHom.finite_algebraMap).mp
  apply finite_left_of_injective _ g hg
  rw [heq]
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp (finite_iterateFrobenius k S p e)

/-- The normalization of an affine domain over a perfect field is finite. After
Noether normalization, the trace bound handles the separable subextension and
a finite Frobenius on the polynomial ring handles the purely inseparable part. -/
theorem finite_affine_normalization (k R : Type*) [Field k] [PerfectField k]
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
  haveI : Module.Finite S (integralClosure S L) := finite_integralClosure_over_polynomial k S K L
  haveI : Module.Finite S B := Module.Finite.equiv
    (IsIntegralClosure.equiv S (integralClosure S L) L B).toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite S R B

/-- In an affine domain over a perfect field, a nonzero nonunit vanishes at the
center of a height-one discrete valuation on the normalization. -/
theorem affine_nonunit_divisor (k R : Type*) [Field k] [PerfectField k]
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
