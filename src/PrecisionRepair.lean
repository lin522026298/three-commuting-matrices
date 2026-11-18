import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section
namespace DVRMinimal
open Matrix
open scoped Matrix
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
abbrev MatS (ι R : Type*) := Matrix ι ι R

/-- Correct a finite-precision left division by P, retaining the supplied
residual matrix. The precision demand is exactly divisibility by t det(P). -/
theorem repairLeft (t : R) (P A L : MatS ι R)
    (h : ∀ i j,t*P.det ∣ (A-P*L) i j) :
    ∃ L₁ : MatS ι R, P*L₁=A ∧ ∀ i j,t ∣ (L₁-L) i j := by
  choose b hb using h
  let B : MatS ι R := Matrix.of b
  have e : A-P*L=(t*P.det) • B := Matrix.ext fun i j => hb i j
  refine ⟨L+t • (P.adjugate*B),?_,?_⟩
  · rw [Matrix.mul_add,Matrix.mul_smul,←Matrix.mul_assoc,Matrix.mul_adjugate,Matrix.smul_mul,
        Matrix.one_mul,smul_smul,←e]; abel
  · intro i j
    rw [add_sub_cancel_left]
    exact ⟨_,rfl⟩

/-- Simultaneously correct both chain maps and the commutator correction.
No exact commutation on the generic free module is assumed or obtained. -/
theorem repairSix (t : R) (P Y Z B D C : MatS ι R) (N : ℕ)
    (hprec : t*P.det ∣ t^N)
    (hY : ∀ i j,t^N ∣ (Y*P-P*B) i j)
    (hZ : ∀ i j,t^N ∣ (Z*P-P*D) i j)
    (hC : ∀ i j,t^N ∣ (Y*Z-Z*Y-P*C) i j) :
    ∃ B' D' C' : MatS ι R, Y*P=P*B' ∧ Z*P=P*D' ∧ Y*Z-Z*Y=P*C' ∧
      (∀ i j,t∣(B'-B) i j) ∧ (∀ i j,t∣(D'-D) i j) ∧ (∀ i j,t∣(C'-C) i j) := by
  obtain ⟨B',eB,dB⟩ := repairLeft t P (Y*P) B fun i j => hprec.trans (hY i j)
  obtain ⟨D',eD,dD⟩ := repairLeft t P (Z*P) D fun i j => hprec.trans (hZ i j)
  obtain ⟨C',eC,dC⟩ := repairLeft t P (Y*Z-Z*Y) C fun i j => hprec.trans (hC i j)
  exact ⟨B',D',C',eB.symm,eD.symm,eC.symm,dB,dD,dC⟩

open PowerSeries in
theorem exact_order_precision {k : Type*} [Field k] (p : PowerSeries k) (N : ℕ)
    (ha : p.order < N) : (X:PowerSeries k)*p ∣ X^N := by
  have hp : p ≠ 0 := by intro eq; simp [eq] at ha
  have hlt : p.order.toNat < N := by
    rwa [←coe_toNat_order hp,ENat.natCast_lt_natCast] at ha
  have hd : p.divXPowOrder ∣ (1:PowerSeries k) := (isUnit_divided_by_X_pow_order hp).dvd
  obtain ⟨v,hv⟩ := hd
  let a := p.order.toNat
  let j := N-(a+1)
  have hj : 1+a+j = N := by dsimp [a,j]; omega
  have hfac : X^a*p.divXPowOrder=p := X_pow_order_mul_divXPowOrder
  refine ⟨X^j*v,?_⟩
  calc
    (X : PowerSeries k)^N = X^(1+a+j) := by rw [hj]
    _ = (X*X^a*X^j)*1 := by rw [pow_add,pow_add,pow_one,mul_one]
    _ = X*p*(X^j*v) := by
      calc
        _ = (X*X^a*X^j)*(p.divXPowOrder*v) := congrArg ((X*X^a*X^j)*·) hv
        _ = X*(X^a*p.divXPowOrder)*(X^j*v) := by ring
        _ = _ := congrArg (fun b : PowerSeries k => X*b*(X^j*v)) hfac

#print axioms repairLeft
#print axioms repairSix
#print axioms exact_order_precision
end DVRMinimal
