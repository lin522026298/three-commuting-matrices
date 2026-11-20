module

public import HeadPresentation
public import ActualMinimalEnds

@[expose] public section
noncomputable section
namespace GKEnds
open Module LinearMap Submodule PowerSeries DivisorG3
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev redM (Y : sq k ι) := constantCoeff.mapMatrix Y

theorem reduce_mv (Y : sq k ι) (v : Row k ι) :
    (redM Y).mulVecLin (reduceVec k ι v) = reduceVec k ι (Y.mulVecLin v) := by
  ext i
  change (∑ j,constantCoeff (Y i j) * constantCoeff (v j)) = constantCoeff (∑ j,Y i j*v j)
  rw [map_sum]; simp only [map_mul]

theorem reduce_shift (Y : sq k ι) (a : k) (v : Row k ι) :
    (redM Y-a • 1).mulVecLin (reduceVec k ι v) =
      reduceVec k ι (Y.mulVecLin v) - a • reduceVec k ι v := by
  change (redM Y-a • 1) *ᵥ (reduceVec k ι v) = _
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  exact congrArg (· - a • reduceVec k ι v) (reduce_mv Y v)

section Source
variable {A : Type*} [CommRing A] [Algebra k A] (P : sq k ι)
variable [Module A (QP P)] [IsScalarTower k A (QP P)]
variable (t : A) (xt : ∀ w : QP P, t • w = (X : O k) • w)

def toSourceHead : HH P ≃ₗ[k] ActualHead (M:=QP P) t :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [tImage_restrictScalars]
    exact congrArg LinearMap.range (LinearMap.ext (fun w => (xt w).symm)))) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv k _

def sourceHead [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι) :
    (ι → k) ≃ₗ[k] ActualHead (M:=QP P) t :=
  (LinearEquiv.ofBijective (headFrame P) ⟨frame_inj_of_eq P hw,frame_surj P⟩) ≪≫ₗ
    toSourceHead P t xt

omit [DecidableEq ι] in
theorem sourceHead_red [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι)
    (v : Row k ι) : sourceHead P t xt hw (reduceVec k ι v) =
      headProjection t (P.mulVecLin.range.mkQ v) := by
  change toSourceHead P t xt (headFrame P (reduceVec k ι v)) = _
  rw [frame_eq]; rfl

def toSourceTail : Tail (X : O k) P.mulVecLin ≃ₗ[k] tKernel (M:=QP P) t where
  toFun w := ⟨w.1,(xt w.1).trans w.2⟩
  invFun w := ⟨w.1,(xt w.1).symm.trans w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include xt in
theorem centered_frames [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι)
    (hp : P.det ≠ 0) :
    ∃ (H : (ι → k) ≃ₗ[k] ActualHead (M:=QP P) t) (D : (ι → k) ≃ₗ[k] tKernel (M:=QP P) t),
      ∀ (Y Y' : sq k ι) (_eq : Y*P=P*Y') (a : k) (y : A),
        (∀ v, y • P.mulVecLin.range.mkQ v = P.mulVecLin.range.mkQ (Y.mulVecLin v) - a • P.mulVecLin.range.mkQ v) →
        (∀ v, H ((redM Y - a • 1).mulVecLin v) = y • H v) ∧
        (∀ v, D ((redM Y' - a • 1).mulVecLin v) = y • D v) := by
  have p0 := constant_P_zero P hw
  obtain ⟨Q,e,_,ev,et⟩ := actual_tail P hp (fun i j => congrFun (congrFun p0 i) j)
  let H := sourceHead P t xt hw
  let D := e ≪≫ₗ toSourceTail P t xt
  refine ⟨H,D,?_⟩
  intro Y Y' eq a y hy
  constructor
  · intro z
    obtain ⟨v,rfl⟩ := reduceVec_surj z
    have hh := congrArg ((headProjection t).restrictScalars k) (hy v)
    have eH (w : Row k ι) : H (reduceVec k ι w) = headProjection t (P.mulVecLin.range.mkQ w) :=
      sourceHead_red P t xt hw w
    rw [reduce_shift,map_sub,map_smul,eH,eH]
    calc _ = ((headProjection t).restrictScalars k) (y • P.mulVecLin.range.mkQ v) := by
               simpa only [map_sub,map_smul,LinearMap.restrictScalars_apply] using hh.symm
         _ = _ := (headProjection t).map_smul y _
  · intro z
    obtain ⟨v,rfl⟩ := reduceVec_surj z
    apply Subtype.ext
    rw [reduce_shift,map_sub,map_smul]
    change (e (reduceVec k ι (Y'.mulVecLin v))).val - a • (e (reduceVec k ι v)).val =
      y • (e (reduceVec k ι v)).val
    rw [et Y Y' eq,ev]
    exact (hy (Q.mulVecLin v)).symm

end Source
end GKEnds
