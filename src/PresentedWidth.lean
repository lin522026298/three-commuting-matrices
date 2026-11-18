import ActualEnds
import ActorIndex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
noncomputable section
namespace GKDivisor.Jet
open PowerSeries DivisorG3 Module LinearMap Submodule
open scoped Matrix

variable {F : Type*} [Field F] {r : ℕ}
abbrev redP (P : Matrix (Fin r) (Fin r) (PowerSeries F)) :=
  (PowerSeries.constantCoeff (R:=F)).mapMatrix P

def cvec : (Fin r → F) →ₗ[F] (Fin r → PowerSeries F) where
  toFun v i := C (v i)
  map_add' _ _ := funext fun _ => map_add .. 
  map_smul' x v := by funext i; change C (x * v i) = x • C (v i); rw [map_mul,PowerSeries.smul_eq_C_mul]

theorem red_cvec (v : Fin r → F) : reduceVec F (Fin r) (cvec v) = v :=
  funext fun _ => constantCoeff_C _

theorem red_mul (P : Matrix (Fin r) (Fin r) (PowerSeries F)) (v : Fin r → PowerSeries F) :
    reduceVec F (Fin r) (P.mulVecLin v) = (redP P).mulVecLin (reduceVec F (Fin r) v) := by
  ext i
  exact (RingHom.map_mulVec (f:=PowerSeries.constantCoeff (R:=F)) P v i)

section
variable (P : Matrix (Fin r) (Fin r) (PowerSeries F))
variable (t : Module.End F (QP P)) (hx : ∀ w, t w = (PowerSeries.X : PowerSeries F) • w)

private def headMap := t.range.mkQ.comp (P.mulVecLin.range.mkQ.restrictScalars F)
include hx in
private theorem head_absorb (v : Fin r → PowerSeries F) :
    headMap P t (cvec (reduceVec F (Fin r) v)) = headMap P t v := by
  have h0 : cvec (reduceVec F (Fin r) v) - v ∈ (reduceVec F (Fin r)).ker := by
    rw [LinearMap.mem_ker,map_sub,red_cvec,sub_self]
  rw [reduceVec_ker] at h0
  obtain ⟨z,hz⟩ := h0
  rw [←sub_eq_zero,←map_sub,←hz]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨P.mulVecLin.range.mkQ z, by rw [hx]; exact (P.mulVecLin.range.mkQ.map_smul X z).symm⟩

def headFromConstants := (headMap P t).comp cvec
include hx in
theorem head_surj : Function.Surjective (headFromConstants P t) := by
  intro x
  obtain ⟨w,rfl⟩ := t.range.mkQ_surjective x
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  exact ⟨reduceVec F (Fin r) v,head_absorb P t hx v⟩

include hx in
theorem head_kernel : (headFromConstants P t).ker = (redP P).mulVecLin.range := by
  ext v
  constructor
  · intro hv
    have hv' : P.mulVecLin.range.mkQ (cvec v) ∈ t.range := (Submodule.Quotient.mk_eq_zero _).mp hv
    obtain ⟨w,hw⟩ := hv'
    obtain ⟨a,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    rw [hx,←map_smul] at hw
    obtain ⟨b,hb⟩ := (Submodule.Quotient.eq _).mp hw.symm
    refine ⟨reduceVec F (Fin r) b,?_⟩
    rw [←red_mul,hb,map_sub,red_cvec]
    have : reduceVec F (Fin r) ((PowerSeries.X : PowerSeries F) • a) = 0 :=
      funext fun i => by change constantCoeff (X*a i)=0; simp
    rw [this,sub_zero]
  · rintro ⟨w,rfl⟩
    have e := head_absorb P t hx (P.mulVecLin (cvec w))
    rw [red_mul,red_cvec] at e
    change headMap P t (cvec ((redP P).mulVecLin w)) = 0
    rw [e]
    change t.range.mkQ (P.mulVecLin.range.mkQ (P.mulVecLin (cvec w))) = 0
    have h0 : P.mulVecLin.range.mkQ (P.mulVecLin (cvec w)) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩
    rw [h0,map_zero]

include hx in
theorem actual_kernel_plus_residue_rank [FiniteDimensional F (QP P)] :
    finrank F t.ker + (redP P).rank = r := by
  let f := headFromConstants P t
  have hh := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (head_surj P t hx),finrank_top, head_kernel P t hx,
    Module.finrank_pi,Fintype.card_fin] at hh
  have eq1 := t.finrank_range_add_finrank_ker
  have eq2 := t.range.finrank_quotient_add_finrank
  change finrank F (QP P ⧸ t.range) + (redP P).rank = r at hh
  omega
end
#print axioms GKDivisor.Jet.actual_kernel_plus_residue_rank
end GKDivisor.Jet
