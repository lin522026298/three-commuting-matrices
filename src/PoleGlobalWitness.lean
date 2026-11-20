module

public import NativePoleEnds
public import GKGraphShifted

@[expose] public section
set_option linter.style.haveILetI false
noncomputable section
namespace GKDivisor.Jet
open PowerSeries Module Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] [CharZero k] {r : ℕ} {s : GKGraph.selectCols r}

abbrev ClosedF (B : BadPole k r (GKGraph.universalMinor k r s)) :=
  AlgebraicClosure (IsLocalRing.ResidueField B.V)
def graphAtClosure (B : BadPole k r (GKGraph.universalMinor k r s)) : GKGraph.ring k r →ₐ[k] ClosedF B :=
  (IsScalarTower.toAlgHom k (IsLocalRing.ResidueField B.V) (ClosedF B)).comp B.residualMap

omit [CharZero k] in
theorem closureField_count (B : BadPole k r (GKGraph.universalMinor k r s)) :
    Algebra.trdeg k (GKGraph.residueCoordinates k r (graphAtClosure B)) + 1 = (3*r*r : ℕ) := by
  rw [graphAtClosure,←GKGraph.coords_trdeg_map]
  exact B.field_count

omit [CharZero k] in
/-- Literal matrices, not merely entries up to conjugacy, agree with the reduced
graph data used in the Jordan count. -/
theorem matrices_at_center {E : Type u} [Field E] [Algebra k E] (S : SeriesPole k E r s)
    (φ : GKGraph.ring k r →ₐ[k] E) (hs : constEntries S.T = φ ∘ GKGraph.gcoord k r)
    (i : Fin 6) : GKGraph.reducedMatrices k r φ i = redP (S.T i) := by
  ext p q
  exact (congrFun hs (i,p,q)).symm

/-- Output packet for the remaining nilpotent-pair argument. The actual ambient module is
the quotient of the same matrix P whose constants constitute the graph specialization. -/
theorem bad_pole_minimal_actual (B : BadPole k r (GKGraph.universalMinor k r s)) (hr : 0<r)
    (small : ∀ j<r, DVRMinimal.SafeEverywhere.{u} j) :
    ∃ S : SeriesPole k (ClosedF B) r s,
      constEntries S.T = graphAtClosure B ∘ GKGraph.gcoord k r ∧
      Algebra.trdeg k (GKGraph.residueCoordinates k r (graphAtClosure B)) + 1 = (3*r*r : ℕ) ∧
      redP (S.T 0) = 0 ∧
      finrank (ClosedF B) (S.native 0).ker = r ∧
      letI : FiniteDimensional (ClosedF B) S.carrier := (S.native_facts hr).1
      ∃ (χ : Fin 3 → ClosedF B) (_ : χ 0=0) (hn : ∀ i,IsNilpotent (shifted S.native χ i)),
        DVRMinimal.TwoEnds (FiniteNilTriple.of S.carrier (shifted S.native χ)
          (shifted_commute S.native χ (S.native_facts hr).2.2.1) hn) ∧
        finrank (ClosedF B) S.carrier < finrank (ClosedF B) (Generated (shifted S.native χ)) := by
  letI : CharZero (ClosedF B) := charZero_of_injective_algebraMap (algebraMap k (ClosedF B)).injective
  obtain ⟨S,hs⟩ := pole_to_algebraic_closure B
  have ⟨eq,zero⟩ := S.minimal_width hr small
  exact ⟨S,hs,closureField_count B,zero,eq,S.minimal_nil_ends hr small⟩

#print axioms GKDivisor.Jet.bad_pole_minimal_actual
end GKDivisor.Jet
