import AffineNormalization
import ResidueDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

set_option linter.style.haveILetI false
noncomputable section
namespace GKDivisor
universe u

theorem trdeg_residueField (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (P : Ideal R) [P.IsPrime] :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k (R ⧸ P) := by
  haveI : Algebra.IsAlgebraic (R ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (R ⧸ P))
  rw [← trdeg_add_eq k (R ⧸ P) (A := P.ResidueField), trdeg_eq_zero_iff.mpr this, add_zero]

abbrev Norm (R : Type*) [CommRing R] := integralClosure R (FractionRing R)

/-- This prime and its DVR are produced from q itself.
The residue field has precisely one fewer transcendence parameter over k. -/
theorem affine_pole_residue (k R : Type u) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal (Norm R), ∃ hp : P.IsPrime, algebraMap R (Norm R) q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime (Norm R) _ P hp) ∧
      Algebra.trdeg k (@Ideal.ResidueField (Norm R) _ P hp) + 1 = Algebra.trdeg k R := by
  obtain ⟨P,hp,hm,hheight,hdvr⟩ := affine_nonunit_divisor k R q hq hn
  haveI : P.IsPrime := hp
  haveI : Module.Finite R (Norm R) := finite_affine_normalization k R
  haveI : Algebra.FiniteType k (Norm R) := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) (inferInstance : Algebra.FiniteType R (Norm R))
  have hN : Algebra.trdeg k (Norm R) = Algebra.trdeg k R :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k R (Norm R))
      (fun a b e => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val e))
      (algebraMap_isIntegral_iff.mpr inferInstance)
  refine ⟨P,hp,hm,hheight,hdvr,?_⟩
  rw [trdeg_residueField, affine_heightOne_dimension k (Norm R) P hheight,hN]

#print axioms GKDivisor.affine_pole_residue
end GKDivisor
