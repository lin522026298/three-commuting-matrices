module

public import TrueMinorTransfer
public import ActorIndex
public import GKGraphCoordinates

@[expose] public section
noncomputable section
namespace GKDivisor
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] {r : ℕ}
open IsDiscreteValuationRing

/-- Intrinsic failure for the presented two-generator actor, keeping the common DVR scalar. -/
def BadDatum {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (T : Fin 6 → GKGraph.Mat V r) (rel : GKGraph.Relations r T) : Prop :=
  Module.length V (DivisorG3.QP (T 0)) <
    Module.length V (DivisorG3.actor (T 0) (T 1) (T 3) (T 2) (T 4) rel.y.symm rel.z.symm)

theorem badDatum_iff_strict {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (T : Fin 6 → GKGraph.Mat V r) (rel : GKGraph.Relations r T) (hd : (T 0).det ≠ 0)
    (hr : 0 < r) :
    BadDatum T rel ↔ ∃ s, addVal V (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) <
      addVal V ((T 0).det^(r-1)) := by
  let M := fun (m : ℕ) => ∃ j : (Fin r × Fin r) → (Fin r × Fin r) ⊕ (Fin m × Fin m),
    addVal V (((DivisorG3.blockColumns (T 0) (DivisorG3.box (T 1) (T 2) m m)).submatrix id j).det) <
      addVal V ((T 0).det^(m-1))
  have hh : BadDatum T rel ↔ M (Fintype.card (Fin r)) :=
    DivisorG3.bad_iff_minor (T 0) (T 1) (T 3) (T 2) (T 4) (T 5) hd
      (by simpa using hr) rel.y.symm rel.z.symm rel.comm.symm
  rw [Fintype.card_fin] at hh
  exact hh

namespace BadPole
variable {s : GKGraph.selectCols r} (B : BadPole k r (GKGraph.universalMinor k r s))

theorem bad (hr : 0 < r) : BadDatum B.matrices B.matrix_relations :=
  (badDatum_iff_strict _ _ B.det_ne_zero hr).mpr ⟨s,B.same_minor_strict⟩

def residualMap := (IsScalarTower.toAlgHom k B.V (IsLocalRing.ResidueField B.V)).comp B.f

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem field_count :
    Algebra.trdeg k (GKGraph.residueCoordinates k r B.residualMap) + 1 = (3*r*r : ℕ) := by
  let S := Set.range (B.residualMap ∘ GKGraph.gcoord k r)
  have hi : Algebra.IsAlgebraic (Algebra.adjoin k S) (IntermediateField.adjoin k S) := inferInstance
  change Algebra.trdeg k (IntermediateField.adjoin k S) + 1 = _
  rw [← trdeg_add_eq k (Algebra.adjoin k S) (A := IntermediateField.adjoin k S),
    trdeg_eq_zero_iff.mpr hi, add_zero]
  exact B.count
end BadPole

/-- End-to-end pole transfer for actual bad DVR data. The target automatically has
an actual bad presented module, and its six reduced matrices generate a field of exact
transcendence degree 3r²−1. -/
theorem actual_bad_transfer [PerfectField k] {V : Type*} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra k V] (hr : 0 < r) (T : Fin 6 → GKGraph.Mat V r)
    (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T) (bad : BadDatum T hT) :
    ∃ s : GKGraph.selectCols r, Nonempty (BadPole k r (GKGraph.universalMinor k r s)) := by
  obtain ⟨s,hs⟩ := (badDatum_iff_strict T hT ht hr).mp bad
  exact ⟨s,strict_pole_of_real_minor k r T ht hT s hs⟩

#print axioms GKDivisor.actual_bad_transfer
#print axioms GKDivisor.BadPole.bad
#print axioms GKDivisor.BadPole.field_count
end GKDivisor
