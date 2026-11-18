import GraphLifts
import ActorIndex
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix
open scoped Matrix
variable {V ι W : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module V W]
omit [IsDomain V] [IsDiscreteValuationRing V] [DecidableEq ι] in
theorem conjugate_length (P Y Y' Z Z' : Matrix ι ι V) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (e : QP P ≃ₗ[V] W) (y z : End V W)
    (hy : ∀ v, e (P.mulVecLin.range.mkQ (Y *ᵥ v))= y (e (P.mulVecLin.range.mkQ v)))
    (hz : ∀ v, e (P.mulVecLin.range.mkQ (Z *ᵥ v))= z (e (P.mulVecLin.range.mkQ v))) :
    length V (actor P Y Y' Z Z' sy sz) = length V (Algebra.adjoin V ({y,z}:Set _)) := by
  let g := e.conjAlgEquiv V
  have trans (B B' : Matrix ι ι V) (s : B*P=P*B') (b : End V W)
      (hb : ∀ v, e (P.mulVecLin.range.mkQ (B *ᵥ v))=b (e (P.mulVecLin.range.mkQ v))) :
      g (liftEnd P B B' s)=b := by
    apply LinearMap.ext
    intro w
    obtain ⟨u,rfl⟩ := e.surjective w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective u
    change e (liftEnd P B B' s (e.symm (e _))) = _
    rw [e.symm_apply_apply,lift_apply,hb]
  let A := actor P Y Y' Z Z' sy sz
  have hm : A.map g.toAlgHom = Algebra.adjoin V ({y,z}:Set _) := by
    rw [show A=Algebra.adjoin V ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _) from rfl,
      AlgHom.map_adjoin,Set.image_insert_eq,Set.image_singleton]
    rw [show g.toAlgHom (liftEnd P Y Y' sy)=y from trans _ _ sy y hy,
      show g.toAlgHom (liftEnd P Z Z' sz)=z from trans _ _ sz z hz]
  change length V A=_
  rw [←hm]
  exact LinearEquiv.length_eq (R:=V) (Subalgebra.equivMapOfInjective A g.toAlgHom g.injective).toLinearEquiv
#print axioms conjugate_length
end DivisorG3
