module

public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section
namespace DVRMinimal
open Polynomial
variable (F : Type*) [Field F] (N : ℕ)

def polyToSeriesJet := (Ideal.Quotient.mk (Ideal.span {PowerSeries.X^N} : Ideal (PowerSeries F))).comp
  (Polynomial.coeToPowerSeries.ringHom : F[X] →+* PowerSeries F)

theorem seriesJet_ker : RingHom.ker (polyToSeriesJet F N)=Ideal.span {(X:F[X])^N} := by
  ext p
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk _ (p : PowerSeries F)=0 ↔ p∈_
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,Ideal.mem_span_singleton,
    Polynomial.X_pow_dvd_iff,PowerSeries.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

theorem seriesJet_surj : Function.Surjective (polyToSeriesJet F N) := by
  rintro y
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨f.trunc N,?_⟩
  change Ideal.Quotient.mk _ (f.trunc N : PowerSeries F)=Ideal.Quotient.mk _ f
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton,PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub,PowerSeries.coeff_coe_trunc_of_lt hi,sub_self]

def polySeriesJetEquiv :
    (F[X] ⧸ Ideal.span {(X:F[X])^N}) ≃+* PowerSeries F ⧸ Ideal.span {(PowerSeries.X:PowerSeries F)^N} :=
  (Ideal.quotEquivOfEq (seriesJet_ker F N).symm).trans
    (RingHom.quotientKerEquivOfSurjective (seriesJet_surj F N))

theorem polySeriesJetEquiv_apply (p : F[X]) :
    polySeriesJetEquiv F N (Ideal.Quotient.mk _ p)=Ideal.Quotient.mk _ (p : PowerSeries F) := rfl

#print axioms polySeriesJetEquiv
end DVRMinimal
