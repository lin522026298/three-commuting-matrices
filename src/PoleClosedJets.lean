import PoleJets
import ActualClosedJet
noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] [CharZero k] {r : ℕ} {s : GKGraph.selectCols r}

/-- There is no bound on the size of the target coefficient field, and no cost in
transcendence degree of the six matrices themselves. The original coordinates are carried
by the *specified* inclusion. -/
theorem pole_to_extended_series (B : BadPole k r (GKGraph.universalMinor k r s))
    {E : Type u} [Field E] [Algebra k E] (e : IsLocalRing.ResidueField B.V →ₐ[k] E) :
    ∃ S : SeriesPole k E r s, constEntries S.T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
  obtain ⟨a,d,ha,hd,hl⟩ := pole_orders B
  obtain ⟨t,ht⟩ := exists_irreducible B.V
  obtain ⟨T,rel,hA,hD,hc⟩ := DVRMinimal.actual_closed_jet r k E e.toRingHom B.matrices B.matrix_relations
    s t ht a d (a+d+1) ha hd (by omega) (by omega)
  obtain ⟨S,_,hs⟩ := realize_series B e a d hl T rel hA hD hc
  exact ⟨S,hs⟩

theorem pole_to_algebraic_closure (B : BadPole k r (GKGraph.universalMinor k r s)) :
    ∃ S : SeriesPole k (AlgebraicClosure (IsLocalRing.ResidueField B.V)) r s,
      constEntries S.T =
        (algebraMap (IsLocalRing.ResidueField B.V) (AlgebraicClosure (IsLocalRing.ResidueField B.V))) ∘
          B.residualMap ∘ GKGraph.gcoord k r := by
  exact pole_to_extended_series B (IsScalarTower.toAlgHom k _ _)

#print axioms GKDivisor.Jet.pole_to_algebraic_closure
end GKDivisor.Jet
