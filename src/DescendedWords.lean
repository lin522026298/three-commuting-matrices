import BoxWords
import BlockIndex
noncomputable section
namespace DivisorG3
open Module Submodule LinearMap Matrix Polynomial
open scoped Matrix
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
def liftEnd (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') : End R (QP P) :=
  P.mulVecLin.range.mapQ _ Y.mulVecLin <| by
    rintro _ ⟨u,rfl⟩
    refine ⟨Y' *ᵥ u,?_⟩
    change P *ᵥ (Y' *ᵥ u) = Y *ᵥ (P *ᵥ u)
    simp only [mulVec_mulVec,sy]
omit [DecidableEq ι] in
theorem lift_apply (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') (v) :
    liftEnd P Y Y' sy (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ (Y *ᵥ v) := rfl

omit [DecidableEq ι] in
theorem lift_comm (P Y Y' Z Z' C : Matrix ι ι R) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (sc : Y*Z-Z*Y=P*C) : Commute (liftEnd P Y Y' sy) (liftEnd P Z Z' sz) := by
  apply LinearMap.ext; intro w
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  change P.mulVecLin.range.mkQ (Y *ᵥ (Z *ᵥ v)) = P.mulVecLin.range.mkQ (Z *ᵥ (Y *ᵥ v))
  rw [← sub_eq_zero,←map_sub]; apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨C *ᵥ v,?_⟩
  change P *ᵥ (C *ᵥ v) = Y *ᵥ (Z *ᵥ v) - Z *ᵥ (Y *ᵥ v)
  rw [mulVec_mulVec,mulVec_mulVec,mulVec_mulVec,←sub_mulVec,sc]

theorem power_intertwines (P Y : Matrix ι ι R) (y : End R (QP P))
    (hy : ∀ v, y (P.mulVecLin.range.mkQ v)=P.mulVecLin.range.mkQ (Y *ᵥ v)) (a : ℕ) (v) :
    (y^a) (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ ((Y^a) *ᵥ v) := by
  induction a generalizing v with
  | zero => simp
  | succ a ih =>
    rw [pow_succ',pow_succ',mul_apply_eq_comp,ih,hy,mulVec_mulVec]
theorem poly_intertwines (P Y : Matrix ι ι R) (y : End R (QP P))
    (hy : ∀ v, y (P.mulVecLin.range.mkQ v)=P.mulVecLin.range.mkQ (Y *ᵥ v)) (p : R[X]) (v) :
    (aeval y p) (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ ((aeval Y p) *ᵥ v) := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,LinearMap.add_apply,add_mulVec,hf,hg]
  | monomial n c =>
    rw [aeval_monomial,aeval_monomial,←Algebra.smul_def,←Algebra.smul_def,
      LinearMap.smul_apply,smul_mulVec,map_smul,power_intertwines _ _ _ hy]
theorem local_charpoly (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') :
    aeval (liftEnd P Y Y' sy) Y.charpoly = 0 := by
  apply LinearMap.ext; intro w
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  simpa [Matrix.aeval_self_charpoly] using poly_intertwines P Y _ (lift_apply P Y Y' sy) Y.charpoly v

def evalAll (P : Matrix ι ι R) : End R (QP P) →ₗ[R] (ι → QP P) :=
  { toFun := fun f j => f (P.mulVecLin.range.mkQ ((Pi.basisFun R ι) j))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
omit [DecidableEq ι] in
theorem evalAll_inj (P : Matrix ι ι R) : Function.Injective (evalAll P) := by
  intro f g eq
  have h : f.comp P.mulVecLin.range.mkQ = g.comp P.mulVecLin.range.mkQ :=
    (Pi.basisFun R ι).ext fun j => congrFun eq j
  apply LinearMap.ext; intro w; obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  exact LinearMap.congr_fun h v

variable [Nontrivial R]
theorem box_image_eq (P Y Y' Z Z' C : Matrix ι ι R) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (sc : Y*Z-Z*Y=P*C) :
    ((Algebra.adjoin R ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _)).toSubmodule).map (evalAll P) =
    wordImage P (box Y Z (Fintype.card ι) (Fintype.card ι)) := by
  let y := liftEnd P Y Y' sy
  let z := liftEnd P Z Z' sz
  have hb := adjoin_box y z (lift_comm _ _ _ _ _ _ sy sz sc) Y.charpoly Z.charpoly
    Y.charpoly_monic Z.charpoly_monic (local_charpoly _ _ _ sy) (local_charpoly _ _ _ sz)
  rw [Matrix.charpoly_natDegree_eq_dim,Matrix.charpoly_natDegree_eq_dim] at hb
  change (Algebra.adjoin R ({y,z}:Set _)).toSubmodule.map (evalAll P) = _
  rw [hb,Submodule.map_span,←Set.range_comp,wordImage]
  congr 2; funext ij j
  change (y^ij.1.val) ((z^ij.2.val) (P.mulVecLin.range.mkQ ((Pi.basisFun R ι) j))) =
    P.mulVecLin.range.mkQ ((Y^ij.1.val * Z^ij.2.val).col j)
  rw [power_intertwines _ _ _ (lift_apply P Z Z' sz),power_intertwines _ _ _ (lift_apply P Y Y' sy),mulVec_mulVec]
  simp [Pi.basisFun_apply]
#print axioms local_charpoly
#print axioms lift_comm
#print axioms box_image_eq
end DivisorG3
