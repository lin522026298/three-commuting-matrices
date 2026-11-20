module

public import PoleGlobalWitness
public import OriginalGraph
public import TripleFamily
public import InitialMinimum

@[expose] public section
noncomputable section
namespace G3Assembly
open Module LinearMap DivisorG3 GKDivisor GKDivisor.Jet GKGraph IsDiscreteValuationRing
open Gerstenhaber.FourBlocks.PrimaryDecomposition DVRMinimal
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
/-- The selected index is literally the same on the original minimal seed and the closed jet.
The coefficient field of the jet is the algebraic closure of the intrinsic pole's residue field,
not a substituted copy of the seed field. -/
structure RealWitness (k : Type u) [Field k] [CharZero k] (r : ℕ) where
  seed : Fin 6 → Mat (O k) r
  rel : Relations r seed
  det_ne : (seed 0).det ≠ 0
  s : selectCols r
  low : addVal (O k) (fullMinor r (seed 0) (seed 1) (seed 2) s) < addVal (O k) ((seed 0).det^(r-1))
  pole : BadPole k r (universalMinor k r s)
  arc : SeriesPole k (ClosedF pole) r s
  same_entries : constEntries arc.T = graphAtClosure pole ∘ gcoord k r
  count : Algebra.trdeg k (residueCoordinates k r (graphAtClosure pole)) + 1 = (3*r*r : ℕ)

theorem present_bad {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : Fin 3 → End k W) (hc : ∀ i j, Commute (T i) (T j)) (nil : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T)) :
    let r := finrank k (T 0).ker
    ∃ G : Fin 6 → Mat (O k) r, ∃ rel : Relations r G, (G 0).det ≠ 0 ∧ BadDatum G rel := by
  obtain ⟨P,U,U',V,V',C,hp,su,sv,sc,nw,nb,_,_⟩ :=
    original_graph (T 0) (T 1) (T 2) nil (hc 1 0) (hc 2 0) (hc 1 2)
  let G := ![P,U,V,U',V',C]
  have rel : Relations _ G := ⟨su.symm,sv.symm,sc.symm⟩
  refine ⟨G,rel,hp,?_⟩
  change length (O k) (QP P) < length (O k) (actor P U U' V V' su sv)
  rw [nw,nb]
  change finrank k W < finrank k (Algebra.adjoin k (Set.range T)) at bad
  rw [family_adjoin] at bad
  exact_mod_cast bad

theorem real_pole_at_minimum {r : ℕ} (A : BadAt.{u} r) (hr : 0<r) : Nonempty (RealWitness A.k r) := by
  have h := present_bad A.T A.hc A.hn A.bad
  dsimp only at h
  rw [A.width] at h
  obtain ⟨G,rel,hp,hb⟩ := h
  obtain ⟨s,low⟩ := (badDatum_iff_strict G rel hp hr).mp hb
  obtain ⟨B⟩ := strict_pole_of_real_minor A.k r G hp rel s low
  obtain ⟨S,hs⟩ := pole_to_algebraic_closure B
  exact ⟨⟨G,rel,hp,s,low,B,S,hs,closureField_count B⟩⟩

theorem original_matrix_pole (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j))
    (bad : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r, 2≤r ∧ r≤n ∧ (∀j<r,SafeEverywhere.{u} j) ∧
      ∃ B : BadAt.{u} r, Nonempty (RealWitness B.k r) := by
  obtain ⟨r,hr,rn,⟨B⟩,small⟩ := arbitrary_matrix_to_least_positive k n A hc bad
  exact ⟨r,hr,rn,small,B,real_pole_at_minimum B (by omega)⟩
#print axioms real_pole_at_minimum
#print axioms original_matrix_pole
end G3Assembly
