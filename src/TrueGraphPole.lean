module

public import AffinePoleResidue
public import GKGraphInversePoint
public import GKGraphDimension

@[expose] public section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
noncomputable section
namespace GKDivisor

universe u
variable (k : Type u) [Field k] [PerfectField k] (r : ℕ)

abbrev invGraph (h : GKGraph.ring k r) :=
  GKRational.adj (K := GKGraph.K k r) ((GKGraph.gdelta k r) ^ (r-1)) h

abbrev invCoord (h : GKGraph.ring k r) : invGraph k r h :=
  GKRational.q (K := GKGraph.K k r) _ _

omit [PerfectField k] in
theorem invGraph_trdeg (h : GKGraph.ring k r) :
    Algebra.trdeg k (invGraph k r h) = (3*r*r : ℕ) := by
  apply le_antisymm
  · rw [← GKGraph.field_trdeg k r]
    exact trdeg_le_of_injective ((invGraph k r h).val.restrictScalars k) Subtype.val_injective
  · rw [← GKGraph.ring_trdeg k r]
    exact trdeg_le_of_injective (IsScalarTower.toAlgHom k (GKGraph.ring k r) (invGraph k r h))
      (fun x y e => Subtype.ext (congrArg (fun z : invGraph k r h => (z : GKGraph.K k r)) e))

/-- Divisor data over an affine input domain. -/
def PoleData (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] (q : A) (dim : ℕ) : Prop :=
  ∃ P : Ideal (Norm A), ∃ hp : P.IsPrime,
    algebraMap A (Norm A) q ∈ P ∧ P.height = 1 ∧
    IsDiscreteValuationRing (@Localization.AtPrime _ _ P hp) ∧
    Algebra.trdeg k (@Ideal.ResidueField _ _ P hp) + 1 = dim

theorem mkPoleData (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (q : A) (hq : q ≠ 0) (hn : ¬ IsUnit q) (dim : ℕ)
    (hd : Algebra.trdeg k A = dim) : PoleData k A q dim := by
  obtain ⟨P,hp,hm,hh,hv,ht⟩ := affine_pole_residue k A q hq hn
  exact ⟨P,hp,hm,hh,hv,ht.trans hd⟩

/-- Original graph values, one actual nonzero determinant witness and a nonunit
inverse-minor ratio imply an actual prime-DVR on the finite normalization with residue
field of exact transcendence degree 3r²−1. No assumed divisor or dimension bound. -/
theorem trueGraph_pole {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    PoleData k (invGraph k r h) (invCoord k r h) (3*r*r) := by
  obtain ⟨_,_,_,hq,hnq⟩ := GKGraph.nonunit_inverse_point k r T ht hT h hd w hw hn
  haveI : Algebra.FiniteType k (invGraph k r h) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k (GKGraph.ring k r))
      (inferInstance : Algebra.FiniteType (GKGraph.ring k r) (invGraph k r h))
  exact mkPoleData k _ (invCoord k r h) hq hnq _ (invGraph_trdeg k r h)

#print axioms GKDivisor.trueGraph_pole
end GKDivisor
