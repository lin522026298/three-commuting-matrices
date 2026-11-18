import SquareCover
import DescendedWords
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix
open scoped Matrix
variable {R W ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module R W]
private theorem factor_matrix (P B : Matrix ι ι R) (h : ∀ v, B.mulVecLin v ∈ P.mulVecLin.range) :
    ∃ D, B=P*D := by
  let f := B.mulVecLin.codRestrict P.mulVecLin.range h
  obtain ⟨d,hd⟩ := Module.projective_lifting_property P.mulVecLin.rangeRestrict f P.mulVecLin.surjective_rangeRestrict
  refine ⟨LinearMap.toMatrix' d,Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hd v)).symm

/-- Every genuine commuting end pair lifts to the six unrestricted integral coordinates.
The free lifts are NOT asserted to commute. -/
theorem graph_lifts (π : (ι → R) →ₗ[R] W) (on : Function.Surjective π)
    (P : Matrix ι ι R) (ran : P.mulVecLin.range=π.ker) (y z : End R W) (hc : Commute y z) :
    ∃ Y Y' Z Z' C : Matrix ι ι R, Y*P=P*Y' ∧ Z*P=P*Z' ∧ Y*Z-Z*Y=P*C ∧
      (∀ v, π (Y *ᵥ v)=y (π v)) ∧ (∀ v, π (Z *ᵥ v)=z (π v)) := by
  obtain ⟨f,hf⟩ := Module.projective_lifting_property π (y.comp π) on
  obtain ⟨g,hg⟩ := Module.projective_lifting_property π (z.comp π) on
  let Y := LinearMap.toMatrix' f
  let Z := LinearMap.toMatrix' g
  have hy (v) : π (Y *ᵥ v)=y (π v) := by rw [LinearMap.toMatrix'_mulVec]; exact LinearMap.congr_fun hf v
  have hz (v) : π (Z *ᵥ v)=z (π v) := by rw [LinearMap.toMatrix'_mulVec]; exact LinearMap.congr_fun hg v
  have nul (v) : π (P *ᵥ v)=0 := (show P.mulVecLin v ∈ π.ker from ran ▸ ⟨v,rfl⟩)
  obtain ⟨Y',sy⟩ := factor_matrix P (Y*P) fun v => by
    rw [ran]; change π ((Y*P) *ᵥ v)=0; rw [←mulVec_mulVec,hy,nul,map_zero]
  obtain ⟨Z',sz⟩ := factor_matrix P (Z*P) fun v => by
    rw [ran]; change π ((Z*P) *ᵥ v)=0; rw [←mulVec_mulVec,hz,nul,map_zero]
  obtain ⟨C,sc⟩ := factor_matrix P (Y*Z-Z*Y) fun v => by
    rw [ran]; change π ((Y*Z-Z*Y) *ᵥ v)=0
    rw [sub_mulVec,←mulVec_mulVec,←mulVec_mulVec,map_sub,hy,hz,hz,hy,sub_eq_zero]
    exact LinearMap.congr_fun hc.eq _
  exact ⟨Y,Y',Z,Z',C,sy,sz,sc,hy,hz⟩
#print axioms graph_lifts
end DivisorG3
