module

public import ActualEnds
public import DescendedWords
public import DVRMinors
public import Gerstenhaber.FourBlocks.MinimalSource.BlockClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section
namespace GKEnds
open DivisorG3 Module LinearMap Submodule PowerSeries
open Gerstenhaber.FourBlocks.MinimalSource
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev xop (P : sq k ι) : End k (QP P) := (times (X : O k) (QP P)).restrictScalars k
abbrev HH (P : sq k ι) := QP P ⧸ (xop P).range
def qHead (P : sq k ι) : Row k ι →ₗ[k] HH P :=
  (xop P).range.mkQ.comp (P.mulVecLin.range.mkQ.restrictScalars k)

def constVec (k ι : Type*) [Field k] : (ι → k) →ₗ[k] Row k ι where
  toFun v i := C (v i)
  map_add' v w := by ext i : 1; exact map_add C _ _
  map_smul' s v := by ext i : 1; change C (s*v i)=s • C (v i); rw [PowerSeries.smul_eq_C_mul,map_mul]

def headFrame (P : sq k ι) : (ι → k) →ₗ[k] HH P := (qHead P).comp (constVec k ι)

omit [DecidableEq ι] in
theorem frame_eq (P : sq k ι) (v : Row k ι) :
    headFrame P (reduceVec k ι v) = qHead P v := by
  have hz : constVec k ι (reduceVec k ι v) - v ∈ (reduceVec k ι).ker := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub,sub_eq_zero]
    exact funext fun i => constantCoeff_C _
  rw [reduceVec_ker] at hz
  obtain ⟨z,ez⟩ := hz
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨P.mulVecLin.range.mkQ z,?_⟩
  change (X : O k) • P.mulVecLin.range.mkQ z =
    P.mulVecLin.range.mkQ (constVec k ι (reduceVec k ι v))-P.mulVecLin.range.mkQ v
  rw [←map_smul,←map_sub]
  exact congrArg P.mulVecLin.range.mkQ ez

omit [DecidableEq ι] in
theorem frame_surj (P : sq k ι) : Function.Surjective (headFrame P) := by
  intro x
  obtain ⟨w,rfl⟩ := (xop P).range.mkQ_surjective x
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  exact ⟨_,frame_eq P v⟩

omit [DecidableEq ι] in
theorem width_le (P : sq k ι) [FiniteDimensional k (QP P)] :
    finrank k (xop P).ker ≤ Fintype.card ι := by
  rw [finrank_ker_eq_quotient_range]
  simpa using (LinearMap.finrank_le_finrank_of_surjective (frame_surj P))

omit [DecidableEq ι] in
theorem frame_inj_of_eq (P : sq k ι) [FiniteDimensional k (QP P)]
    (h : finrank k (xop P).ker = Fintype.card ι) : Function.Injective (headFrame P) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Module.finrank_pi,←h,finrank_ker_eq_quotient_range])).mpr (frame_surj P)

theorem constant_P_zero (P : sq k ι) [FiniteDimensional k (QP P)]
    (h : finrank k (xop P).ker = Fintype.card ι) : constantCoeff.mapMatrix P=0 := by
  have inj := frame_inj_of_eq P h
  ext i j
  have hz : headFrame P (reduceVec k ι (P.col j))=0 := by
    rw [frame_eq]; change (xop P).range.mkQ (P.mulVecLin.range.mkQ (P.col j))=0
    have mem : P.col j ∈ P.mulVecLin.range := ⟨Pi.single j 1, by simp⟩
    have hh : P.mulVecLin.range.mkQ (P.col j)=0 := (Submodule.Quotient.mk_eq_zero _).mpr mem
    rw [hh,map_zero]
  exact congrFun (inj (hz.trans (map_zero _).symm)) i

end GKEnds
