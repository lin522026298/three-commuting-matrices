module

public import TrueGraphPole
public import GKRationalResidual

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
namespace GKDivisor
universe u

/-- Coordinate count for a prime on a finite extension N of A when the residue
of A is represented already by the smaller base G. No finiteness G→A is used. -/
theorem trdeg_center_eq (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] [Module.Finite A N]
    (P : Ideal N) [P.IsPrime]
    (hs : Function.Surjective ((Ideal.Quotient.mk (P.under A)).comp (algebraMap G A))) :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k (G ⧸ (P.under A).under G) := by
  let Q := P.under A
  let J := Q.under G
  have hfin : Algebra.trdeg k (N ⧸ P) = Algebra.trdeg k (A ⧸ Q) :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k (A ⧸ Q) (N ⧸ P))
      (FaithfulSMul.algebraMap_injective _ _) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hsurj : Function.Surjective (algebraMap (G ⧸ J) (A ⧸ Q)) := by
    intro v
    obtain ⟨w,hw⟩ := hs v
    exact ⟨Ideal.Quotient.mk J w,hw⟩
  have hinteg : (algebraMap (G ⧸ J) (A ⧸ Q)).IsIntegral :=
    RingHom.isIntegral_of_surjective _ hsurj
  rw [trdeg_residueField, hfin]
  exact trdeg_integral_inj (IsScalarTower.toAlgHom k (G ⧸ J) (A ⧸ Q))
    (FaithfulSMul.algebraMap_injective _ _) hinteg

/-- With an affine input, the ordinary quotient of the original graph
has the full residual transcendence degree, even though the inverse graph need not be finite. -/
def CenterData (k G A : Type u) [Field k] [CommRing G] [CommRing A] [IsDomain A]
    [Algebra k G] [Algebra k A] [Algebra G A] (q : A) (dim : ℕ) : Prop :=
  ∃ P : Ideal (Norm A), ∃ hp : P.IsPrime,
    algebraMap A (Norm A) q ∈ P ∧ P.height = 1 ∧
    IsDiscreteValuationRing (@Localization.AtPrime _ _ P hp) ∧
    Algebra.trdeg k (@Ideal.ResidueField _ _ P hp) + 1 = dim ∧
    Algebra.trdeg k (G ⧸ (P.under A).under G) + 1 = dim

theorem mkCenterData (k G A : Type u) [Field k] [CharZero k] [CommRing G] [CommRing A] [IsDomain A]
    [Algebra k G] [Algebra k A] [Algebra.FiniteType k A] [Algebra G A] [IsScalarTower k G A]
    (q : A) (m : ℕ) (H : PoleData k A q m)
    (he : ∀ Q : Ideal A, q ∈ Q → Function.Surjective ((Ideal.Quotient.mk Q).comp (algebraMap G A))) :
    CenterData k G A q m := by
  obtain ⟨P,hp,hm,hh,hv,ht⟩ := H
  letI := hp
  letI : Module.Finite A (Norm A) := finite_affine_normalization k A
  exact ⟨P,hp,hm,hh,hv,ht,(trdeg_center_eq k G A (Norm A) P (he _ hm)) ▸ ht⟩

variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
theorem trueGraph_pole_center {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    CenterData k (GKGraph.ring k r) (invGraph k r h) (invCoord k r h) (3*r*r) := by
  haveI : Algebra.FiniteType k (invGraph k r h) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k (GKGraph.ring k r))
      (inferInstance : Algebra.FiniteType (GKGraph.ring k r) (invGraph k r h))
  exact mkCenterData k _ _ _ _ (trueGraph_pole k r T ht hT h hd w hw hn)
    (GKRational.residue_surjective _ _)
#print axioms GKDivisor.trueGraph_pole_center
end GKDivisor
