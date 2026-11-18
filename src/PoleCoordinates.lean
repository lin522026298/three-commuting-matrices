import PoleCenter
noncomputable section
namespace GKDivisor
universe u

/-- The actual residual hom through two successive maps; no chosen coefficient-field section. -/
def centerMap (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] (P : Ideal N) [P.IsPrime] :
    G →ₐ[k] P.ResidueField :=
  (IsScalarTower.toAlgHom k N P.ResidueField).comp
    ((IsScalarTower.toAlgHom k A N).comp (IsScalarTower.toAlgHom k G A))

theorem centerMap_range_trdeg (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] (P : Ideal N) [P.IsPrime] :
    Algebra.trdeg k (centerMap k G A N P).range = Algebra.trdeg k (G ⧸ (P.under A).under G) := by
  let f := centerMap k G A N P
  have he : RingHom.ker f = (P.under A).under G := by
    ext x
    exact Ideal.algebraMap_residueField_eq_zero
  exact (Ideal.quotientKerEquivRange f).trdeg_eq.symm.trans (congrArg (fun I : Ideal G => Algebra.trdeg k (G ⧸ I)) he)

theorem six_coordinate_count (k : Type u) [Field k] (r : ℕ) (A N : Type u)
    [CommRing A] [CommRing N] [Algebra k A] [Algebra k N]
    [Algebra (GKGraph.ring k r) A] [Algebra A N]
    [IsScalarTower k (GKGraph.ring k r) A] [IsScalarTower k A N]
    (P : Ideal N) [P.IsPrime] :
    let ψ := centerMap k (GKGraph.ring k r) A N P
    Algebra.trdeg k (Algebra.adjoin k (Set.range (ψ ∘ GKGraph.gcoord k r))) =
      Algebra.trdeg k ((GKGraph.ring k r) ⧸ (P.under A).under (GKGraph.ring k r)) := by
  dsimp only
  rw [← GKGraph.range_generated]
  exact centerMap_range_trdeg k _ _ _ P

#print axioms GKDivisor.six_coordinate_count
end GKDivisor
