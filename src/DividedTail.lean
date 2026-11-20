module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section
noncomputable section
namespace DivisorG3
open LinearMap Module Submodule
variable {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]
abbrev Coker (P : Module.End R F) := F ⧸ P.range
def times (t : R) (F : Type*) [AddCommGroup F] [Module R F] : Module.End R F := t • LinearMap.id
variable (t : R) (P Q : Module.End R F)
abbrev Tail := (times t (Coker P)).ker
def toTail (fac : ∀ x, P x = t • Q x) : F →ₗ[R] Tail t P :=
  (P.range.mkQ.comp Q).codRestrict _ fun x => by
    change t • P.range.mkQ (Q x) = 0
    rw [← map_smul,←fac]
    exact (Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩

theorem toTail_surj (fac : ∀ x, P x = t • Q x)
    (reg : Function.Injective (fun x : F => t • x)) : Function.Surjective (toTail t P Q fac) := by
  rintro ⟨w,hw⟩
  obtain ⟨v,rfl⟩ := P.range.mkQ_surjective w
  change t • P.range.mkQ v=0 at hw
  rw [←map_smul] at hw
  obtain ⟨z,hz⟩ := (Quotient.mk_eq_zero _).mp hw
  have eq : Q z=v := reg ((fac z).symm.trans hz)
  exact ⟨z,Subtype.ext (congrArg P.range.mkQ eq)⟩
theorem toTail_ker (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P) :
    (toTail t P Q fac).ker = (times t F).range := by
  ext x
  change (toTail t P Q fac x = 0) ↔ ∃ z, t • z = x
  rw [Subtype.ext_iff]
  change P.range.mkQ (Q x) = 0 ↔ _
  rw [mkQ_apply,Quotient.mk_eq_zero]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,inj ?_⟩
    rw [map_smul,fac x,←hz]
  · rintro ⟨z,rfl⟩
    exact ⟨z,(fac z).trans (Q.map_smul t z).symm⟩

def tailEquiv (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P)
    (reg : Function.Injective (fun x : F => t • x)) :
    Coker (times t F) ≃ₗ[R] Tail t P :=
  (Submodule.quotEquivOfEq _ _ (toTail_ker t P Q fac inj).symm) ≪≫ₗ
   (toTail t P Q fac).quotKerEquivOfSurjective (toTail_surj t P Q fac reg)

theorem tail_formula (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P)
    (reg : Function.Injective (fun x : F => t • x)) (x : F) :
    (tailEquiv t P Q fac inj reg ((times t F).range.mkQ x)).val = P.range.mkQ (Q x) := rfl

/-- The primed operator acts on the source of the presentation; unprimed acts on the quotient. -/
theorem tail_intertwines (Y Y' : Module.End R F) (fac : ∀ x, P x = t • Q x)
    (reg : Function.Injective (fun x : F => t • x)) (square : ∀ x, Y (P x) = P (Y' x)) (x : F) :
    P.range.mkQ (Q (Y' x)) = P.range.mkQ (Y (Q x)) := by
  apply congrArg _
  apply reg
  change t • Q (Y' x) = t • Y (Q x)
  rw [←fac,←Y.map_smul,←fac, square]
#print axioms tailEquiv
#print axioms tail_formula
#print axioms tail_intertwines
end DivisorG3
