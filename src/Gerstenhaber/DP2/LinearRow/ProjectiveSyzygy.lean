module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Explicit Schanuel comparison for the coefficient-module resolution in
the full linear-row proof. No syzygy projectivity is postulated in the
comparison theorem: it is transported from an actual second resolution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Gerstenhaber.DP2.LinearRow

variable {B : Type*} [CommRing B]
variable {P Q T : Type*} [AddCommGroup P] [Module B P]
  [AddCommGroup Q] [Module B Q] [AddCommGroup T] [Module B T]

/-- The actual fiber product of two module maps to the same target. -/
def mapPullback (f : P →ₗ[B] T) (g : Q →ₗ[B] T) : Submodule B (P × Q) where
  carrier := {v | f v.1 = g v.2}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw; simpa using congrArg₂ HAdd.hAdd hv hw
  smul_mem' := by intro b v hv; simpa using congrArg (b • ·) hv

/-- A chosen lift of `f` across `g` splits the actual pullback. -/
def mapPullbackSplit (f : P →ₗ[B] T) (g : Q →ₗ[B] T)
    (l : P →ₗ[B] Q) (hl : g.comp l = f) :
    (LinearMap.ker g × P) ≃ₗ[B] mapPullback f g where
  toFun v := ⟨(v.2,v.1+l v.2),by
    change f v.2 = g (↑v.1 + l v.2)
    rw [map_add,v.1.property,zero_add]
    exact (DFunLike.congr_fun hl v.2).symm⟩
  invFun v := (⟨v.1.2-l v.1.1,by
    change g (v.1.2-l v.1.1)=0
    have hlv : g (l v.1.1)=f v.1.1 := DFunLike.congr_fun hl v.1.1
    rw [map_sub,hlv]
    exact sub_eq_zero.mpr v.property.symm⟩,v.1.1)
  left_inv v := by ext <;> simp
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact sub_add_cancel _ _
  map_add' v w := by ext <;> simp [add_assoc,add_left_comm,add_comm]
  map_smul' b v := by ext <;> simp [smul_add]

def mapPullbackSwap (f : P →ₗ[B] T) (g : Q →ₗ[B] T) :
    mapPullback f g ≃ₗ[B] mapPullback g f where
  toFun v := ⟨(v.1.2,v.1.1),v.property.symm⟩
  invFun v := ⟨(v.1.2,v.1.1),v.property.symm⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' b v := rfl

/-- Schanuel's isomorphism, constructed through the common pullback. -/
def schanuelEquiv [Module.Projective B P] [Module.Projective B Q]
    (f : P →ₗ[B] T) (g : Q →ₗ[B] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (LinearMap.ker f × Q) ≃ₗ[B] (LinearMap.ker g × P) := by
  let l := Classical.choose (Module.projective_lifting_property g f hg)
  have hl := Classical.choose_spec (Module.projective_lifting_property g f hg)
  let m := Classical.choose (Module.projective_lifting_property f g hf)
  have hm := Classical.choose_spec (Module.projective_lifting_property f g hf)
  exact (mapPullbackSplit g f m hm).trans
    ((mapPullbackSwap g f).trans (mapPullbackSplit f g l hl).symm)

/-- An actual split-off kernel is projective whenever the comparison
kernel is projective. This is the one-step part of the two-syzygy proof. -/
theorem projective_kernel_of_comparison [Module.Projective B P]
    [Module.Projective B Q] (f : P →ₗ[B] T) (g : Q →ₗ[B] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective B (LinearMap.ker g)] :
    Module.Projective B (LinearMap.ker f) := by
  let e := schanuelEquiv f g hf hg
  letI : Module.Projective B (LinearMap.ker f × Q) :=
    Module.Projective.of_equiv' e.symm
  exact Module.Projective.of_split (LinearMap.inl B (LinearMap.ker f) Q)
    (LinearMap.fst B (LinearMap.ker f) Q) (by ext; rfl)

/-- Adding an identity summand does not change the kernel. -/
def kernelProdIdEquiv (f : P →ₗ[B] T) (Q : Type*)
    [AddCommGroup Q] [Module B Q] :
    LinearMap.ker (f.prodMap (LinearMap.id : Q →ₗ[B] Q)) ≃ₗ[B]
      LinearMap.ker f where
  toFun v := ⟨v.1.1,by
    have hv := congrArg Prod.fst v.property
    exact hv⟩
  invFun v := ⟨(v.1,0),by
    apply Prod.ext
    · exact v.property
    · rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hv := congrArg Prod.snd v.property
      exact hv.symm
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' b v := rfl

/-- The actual differential with codomain its augmentation kernel. -/
def syzygyMap {P₁ : Type*} [AddCommGroup P₁] [Module B P₁]
    (f₀ : P →ₗ[B] T) (f₁ : P₁ →ₗ[B] P) (hzero : f₀.comp f₁=0) :
    P₁ →ₗ[B] LinearMap.ker f₀ :=
  f₁.codRestrict (LinearMap.ker f₀) (fun p => DFunLike.congr_fun hzero p)

theorem syzygyMap_surjective {P₁ : Type*} [AddCommGroup P₁] [Module B P₁]
    (f₀ : P →ₗ[B] T) (f₁ : P₁ →ₗ[B] P) (hzero : f₀.comp f₁=0)
    (hexact : LinearMap.range f₁=LinearMap.ker f₀) :
    Function.Surjective (syzygyMap f₀ f₁ hzero) := by
  intro p
  have hp : p.1 ∈ LinearMap.range f₁ := by rw [hexact]; exact p.property
  obtain ⟨v,hv⟩ := hp
  exact ⟨v,Subtype.ext hv⟩

theorem ker_syzygyMap {P₁ : Type*} [AddCommGroup P₁] [Module B P₁]
    (f₀ : P →ₗ[B] T) (f₁ : P₁ →ₗ[B] P) (hzero : f₀.comp f₁=0) :
    LinearMap.ker (syzygyMap f₀ f₁ hzero)=LinearMap.ker f₁ := by
  ext v
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Two actual projective presentations transfer projectivity of the
second syzygy. This is the coefficient-module Schanuel step needed for
`ker(R^μ → R → T)`; the companion file constructs the comparison
resolution explicitly from the two commuting coordinate operators. -/
theorem projective_second_syzygy
    {P₁ Q₁ : Type*} [AddCommGroup P₁] [Module B P₁]
    [AddCommGroup Q₁] [Module B Q₁]
    [Module.Projective B P] [Module.Projective B P₁]
    [Module.Projective B Q] [Module.Projective B Q₁]
    (f₀ : P →ₗ[B] T) (f₁ : P₁ →ₗ[B] P)
    (g₀ : Q →ₗ[B] T) (g₁ : Q₁ →ₗ[B] Q)
    (hf₀ : Function.Surjective f₀) (hg₀ : Function.Surjective g₀)
    (hfzero : f₀.comp f₁=0) (hgzero : g₀.comp g₁=0)
    (hfexact : LinearMap.range f₁=LinearMap.ker f₀)
    (hgexact : LinearMap.range g₁=LinearMap.ker g₀)
    [Module.Projective B (LinearMap.ker g₁)] :
    Module.Projective B (LinearMap.ker f₁) := by
  let e := schanuelEquiv f₀ g₀ hf₀ hg₀
  let a := syzygyMap f₀ f₁ hfzero
  let b := syzygyMap g₀ g₁ hgzero
  have ha := syzygyMap_surjective f₀ f₁ hfzero hfexact
  have hb := syzygyMap_surjective g₀ g₁ hgzero hgexact
  let a' : (P₁ × Q) →ₗ[B] (LinearMap.ker f₀ × Q) :=
    a.prodMap LinearMap.id
  let b' : (Q₁ × P) →ₗ[B] (LinearMap.ker f₀ × Q) :=
    e.symm.toLinearMap.comp (b.prodMap LinearMap.id)
  have ha' : Function.Surjective a' := by
    rintro ⟨p,q⟩
    obtain ⟨v,hv⟩ := ha p
    exact ⟨(v,q),Prod.ext hv rfl⟩
  have hb' : Function.Surjective b' := by
    apply e.symm.surjective.comp
    rintro ⟨q,p⟩
    obtain ⟨v,hv⟩ := hb q
    exact ⟨(v,p),Prod.ext hv rfl⟩
  have hkb : LinearMap.ker b=LinearMap.ker g₁ := ker_syzygyMap g₀ g₁ hgzero
  letI : Module.Projective B (LinearMap.ker b) :=
    Module.Projective.of_equiv' (LinearEquiv.ofEq _ _ hkb).symm
  letI : Module.Projective B (LinearMap.ker (b.prodMap (LinearMap.id : P →ₗ[B] P))) :=
    Module.Projective.of_equiv' (kernelProdIdEquiv b P).symm
  have hkb' : LinearMap.ker b' =
      LinearMap.ker (b.prodMap (LinearMap.id : P →ₗ[B] P)) := by
    exact LinearEquiv.ker_comp e.symm _
  letI : Module.Projective B (LinearMap.ker b') :=
    Module.Projective.of_equiv' (LinearEquiv.ofEq _ _ hkb').symm
  letI : Module.Projective B (LinearMap.ker a') :=
    projective_kernel_of_comparison a' b' ha' hb'
  letI : Module.Projective B (LinearMap.ker a) :=
    Module.Projective.of_equiv' (kernelProdIdEquiv a Q)
  exact Module.Projective.of_equiv'
    (LinearEquiv.ofEq _ _ (ker_syzygyMap f₀ f₁ hfzero))

end Gerstenhaber.DP2.LinearRow
