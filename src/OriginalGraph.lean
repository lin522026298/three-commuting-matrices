import OriginActor
import ConjugateActor
import MinimalCover
noncomputable section
namespace DivisorG3
open Module LinearMap PowerSeries Matrix IsDiscreteValuationRing
open scoped Matrix
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
/-- All original data are ordinary endomorphisms over k, not formal modules or lifts.
The geometric DVR and dimension contradiction are not used here. -/
theorem original_graph (T Y Z : End k W) (ht : IsNilpotent T) (hY : Commute Y T)
    (hZ : Commute Z T) (hYZ : Commute Y Z) :
    let ι := Fin (finrank k T.ker)
    ∃ P U U' V V' C : Matrix ι ι (O k), ∃ _hp : P.det≠0, ∃ su : U*P=P*U', ∃ sv : V*P=P*V',
      U*V-V*U=P*C ∧ length (O k) (QP P) = finrank k W ∧
      length (O k) (actor P U U' V V' su sv)=finrank k (triple T Y Z) ∧
      (∃ E : QP P ≃ₗ[k] W, (∀ w, E ((X : O k) • w)=T (E w)) ∧
        (∀ w, E (liftEnd P U U' su w)=Y (E w)) ∧
        (∀ w, E (liftEnd P V V' sv w)=Z (E w))) ∧
      (finrank k W < finrank k (triple T Y Z) →
        ∃ j, addVal (O k) ((wordLattice P U V).submatrix _root_.id j).det <
          addVal (O k) (P.det^(Fintype.card ι-1))) := by
  obtain ⟨ρ,modW,tower,hX,hr,hρ,⟨a,ha,ann⟩,lift⟩ := original_action T ht
  let _ : Module (O k) W := modW
  let _ : IsScalarTower k (O k) W := tower
  obtain ⟨y,hy⟩ := lift Y hY
  obtain ⟨z,hz⟩ := lift Z hZ
  have comm : Commute y z := by
    apply LinearMap.ext; intro w
    exact LinearMap.congr_fun (show Commute (y.restrictScalars k) (z.restrictScalars k) from hy ▸ hz ▸ hYZ).eq w
  obtain ⟨π,on⟩ := minimal_cover T fun w => (hρ X w).trans (LinearMap.congr_fun hX w)
  obtain ⟨P,hp,ran,e,eq⟩ := square_cover π on a ha ann
  obtain ⟨U,U',V,V',C,su,sv,sc,hu,hv⟩ := graph_lifts π on P ran y z comm
  have nw : length (O k) (QP P)=finrank k W := e.length_eq.trans (actual_length k W)
  have nb : length (O k) (actor P U U' V V' su sv)=finrank k (triple T Y Z) := by
    rw [conjugate_length _ _ _ _ _ su sv e y z (fun w => by rw [eq,eq,hu]) (fun w => by rw [eq,eq,hv])]
    have he := origin_actor_length ρ T hX hr hρ y z
    change length (O k) (pair y z) = _
    convert he using 1; subst_vars; rfl
  refine ⟨P,U,U',V,V',C,hp,su,sv,sc,nw,nb,⟨e.restrictScalars k,?_,?_,?_⟩,?_⟩
  · intro w
    change e ((X : O k) • w)=T (e w)
    rw [map_smul,hρ,hX]
  · intro w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    change e (P.mulVecLin.range.mkQ (U *ᵥ v))=Y (e (P.mulVecLin.range.mkQ v))
    rw [eq,eq,hu]; exact LinearMap.congr_fun hy _
  · intro w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    change e (P.mulVecLin.range.mkQ (V *ᵥ v))=Z (e (P.mulVecLin.range.mkQ v))
    rw [eq,eq,hv]; exact LinearMap.congr_fun hz _
  intro bad
  have pos : 0 < finrank k T.ker := by
    by_contra! h
    let _ : IsEmpty (Fin (finrank k T.ker)) := ⟨fun i => by have := i.isLt; omega⟩
    let _ : Subsingleton W := on.subsingleton
    have hz0 : finrank k (triple T Y Z) = 0 := Module.finrank_zero_of_subsingleton
    omega
  apply (bad_iff_minor _ _ _ _ _ _ hp (by simpa using pos) su sv sc).mp
  rw [nw,nb]
  exact_mod_cast bad
#print axioms original_graph
end DivisorG3
