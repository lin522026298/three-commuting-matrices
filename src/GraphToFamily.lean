module

public import NativeSeries
public import TripleFamily

@[expose] public section
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix PowerSeries IsDiscreteValuationRing
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev nativeTriple (P Y Y' Z Z' : Matrix ι ι (O k)) (sy : Y*P=P*Y') (sz : Z*P=P*Z') :=
  triples (seriesAct k (QP P) X) ((liftEnd P Y Y' sy).restrictScalars k) ((liftEnd P Z Z' sz).restrictScalars k)
theorem strict_to_native (P Y Y' Z Z' C : Matrix ι ι (O k)) (hp : P.det≠0) (hr : 0<Fintype.card ι)
    (sy : Y*P=P*Y') (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C)
    (low : ∃ j, addVal (O k) ((wordLattice P Y Z).submatrix _root_.id j).det <
        addVal (O k) (P.det^(Fintype.card ι-1))) :
    let S := nativeTriple P Y Y' Z Z' sy sz
    FiniteDimensional k (QP P) ∧ IsNilpotent (S 0) ∧ (∀ i j, Commute (S i) (S j)) ∧
      finrank k (QP P)<finrank k (Algebra.adjoin k (Set.range S)) := by
  obtain ⟨fin,hn,hy,hz,hc,nw,nb⟩ := native_graph _ _ _ _ _ _ hp sy sz sc
  refine ⟨fin,hn,triples_comm hy hz hc,?_⟩
  rw [family_adjoin]
  have small := (bad_iff_minor _ _ _ _ _ _ hp hr sy sz sc).mpr low
  rw [nw,nb] at small
  exact_mod_cast small
#print axioms strict_to_native
end DivisorG3
