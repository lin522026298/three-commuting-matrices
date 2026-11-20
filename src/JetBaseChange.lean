module

public import ActualBadTransfer
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing

theorem series_value {F : Type*} [Field F] (f : PowerSeries F) : addVal _ f = f.order := by
  rw [PowerSeries.order_eq_emultiplicity_X,addVal,multiplicity_addValuation_apply]
  exact emultiplicity_eq_of_associated_left
    (associated_of_irreducible _ (PowerSeries.irreducible_X (R:=F)) (Classical.choose_spec (exists_prime _)).irreducible)

theorem order_coeff_extension {F E : Type*} [Field F] [Field E] (e : F →+* E) (f : PowerSeries F) :
    (PowerSeries.map e f).order = f.order := by
  apply PowerSeries.order_eq.mpr
  have H := PowerSeries.order_eq.mp (rfl : f.order=f.order)
  constructor
  · intro i hi
    rw [PowerSeries.coeff_map]
    exact (map_ne_zero_iff _ e.injective).mpr (H.1 i hi)
  · intro i hi
    rw [PowerSeries.coeff_map, H.2 i hi, map_zero]

universe u
/-- The transcendence count of a literal family of coefficients survives any extension of
the coefficient field; only the injective inclusion of those actual coordinates is used. -/
theorem count_extension {k F E : Type u} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    {ι : Type*} (e : F →ₐ[k] E) (x : ι → F) :
    Algebra.trdeg k (Algebra.adjoin k (Set.range (e ∘ x))) =
      Algebra.trdeg k (Algebra.adjoin k (Set.range x)) := by
  rw [Set.range_comp,← AlgHom.map_adjoin]
  exact (Subalgebra.equivMapOfInjective (Algebra.adjoin k (Set.range x)) e e.injective).trdeg_eq.symm

theorem relations_map {V S : Type*} [CommRing V] [CommRing S]
    {r : ℕ} (f : V →+* S) (T : Fin 6 → GKGraph.Mat V r) (hT : GKGraph.Relations r T) :
    GKGraph.Relations r (fun j => f.mapMatrix (T j)) := by
  constructor
  · simpa only [map_mul] using congrArg f.mapMatrix hT.y
  · simpa only [map_mul] using congrArg f.mapMatrix hT.z
  · simpa only [map_sub,map_mul] using congrArg f.mapMatrix hT.comm

#print axioms GKDivisor.Jet.series_value
#print axioms GKDivisor.Jet.count_extension
end GKDivisor.Jet
