import DVRScalar
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
noncomputable section
namespace DivisorG3
open Module PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
/-- Honest formal evaluation at an arbitrary nilpotent linear operator: the range is
exactly its polynomial algebra, not the ambient endomorphism ring. -/
theorem series_of_nil (T : End k W) (ht : IsNilpotent T) :
    ∃ ρ : O k →ₐ[k] End k W, ρ X=T ∧ ρ.range=Algebra.adjoin k ({T}:Set _) := by
  let A := Algebra.adjoin k ({T}:Set _)
  let _ : CommRing A := {(inferInstance : Ring A) with mul_comm := fun x y => mul_comm' x y}
  let u : A := ⟨T,Algebra.self_mem_adjoin_singleton k T⟩
  have hu : IsNilpotent u := by obtain ⟨e,he⟩:=ht; exact ⟨e,Subtype.ext he⟩
  let c : PowerSeries A := C u
  have hc : HasSubst c := by change IsNilpotent (constantCoeff (C u)); simpa using hu
  let sub : O k →ₐ[k] PowerSeries A := substAlgHom hc
  let cc : PowerSeries A →ₐ[k] A := {
    toRingHom := constantCoeff
    commutes' := fun x => constantCoeff_C _ }
  let ρ := A.val.comp (cc.comp sub)
  have hx : ρ X=T := by change ↑(constantCoeff (sub X)) = T; rw [show sub X=c from substAlgHom_X hc]; exact congrArg Subtype.val (constantCoeff_C u)
  refine ⟨ρ,hx,le_antisymm ?_ (Algebra.adjoin_le ?_)⟩
  · rintro _ ⟨z,rfl⟩; exact (cc (sub z)).property
  · rintro _ rfl; exact ⟨X,hx⟩
#print axioms series_of_nil
end DivisorG3
