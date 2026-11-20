module

public import ActualSixJet
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

noncomputable section
namespace DVRMinimal
open scoped Matrix
open GKGraph PowerSeries IsDiscreteValuationRing IsLocalRing
variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem order_injective_map {F L : Type*} [Field F] [Field L] (φ : F →+* L)
    {x : PowerSeries F} {j : ℕ} (hj : x.order=j) : (PowerSeries.map φ x).order=j := by
  obtain ⟨ne,h⟩ := PowerSeries.order_eq_nat.mp hj
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by rwa [coeff_map,ne_eq,map_eq_zero_iff φ φ.injective], fun i hi => by rw [coeff_map,h i hi,map_zero]⟩

theorem actual_closed_jet (r : ℕ) (k : Type*) [Field k] [Algebra k V]
    [Algebra.FormallySmooth k (ResidueField V)]
    (L : Type*) [Field L] (φ : ResidueField V →+* L)
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries L) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = φ (residue V (T l i j)) := by
  obtain ⟨A,hrel,hp,hm,hres⟩ := actual_six_jet r k T hT s u hu a d N hA hD ha hd
  let g := PowerSeries.map φ
  let S : Fin 6 → GKGraph.Mat (PowerSeries L) r := fun i => g.mapMatrix (A i)
  have s1 : Relations r S := by
    constructor
    · exact (map_mul _ _ _).symm.trans ((congrArg g.mapMatrix hrel.y).trans (map_mul _ _ _))
    · exact (map_mul _ _ _).symm.trans ((congrArg g.mapMatrix hrel.z).trans (map_mul _ _ _))
    · have hh := congrArg g.mapMatrix hrel.comm
      simpa only [S,map_mul,map_sub] using hh
  refine ⟨S,s1,?_,?_,?_⟩
  · change (g.mapMatrix (A 0)).det.order=a
    rw [←RingHom.map_det]; exact order_injective_map φ hp
  · change (fullMinor r (g.mapMatrix _) (g.mapMatrix _) (g.mapMatrix _) s).order=d
    rw [←fullMinor_map]; exact order_injective_map φ hm
  · intro l i j
    change constantCoeff (PowerSeries.map φ (A l i j)) = _
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,hres]

#print axioms actual_closed_jet
end DVRMinimal
