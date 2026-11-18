module

public import Gerstenhaber.DP2.LinearRow.ProjectiveSyzygy
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Relative Frobenius adjunction and actual lifting for the full linear-row
proof. The companion monic coefficient model will supply the explicit
functional and prove the pairing bijective.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

namespace Gerstenhaber.DP2.LinearRow

variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The actual relative multiplication pairing defined by a functional. -/
def frobeniusPairing (τ : R →ₗ[B] B) : R →ₗ[B] Module.Dual B R where
  toFun a :=
    { toFun := fun b => τ (a*b)
      map_add' b c := by simp [mul_add]
      map_smul' b c := by
        change τ (a*(b • c))=b • τ (a*c)
        rw [Algebra.mul_smul_comm,τ.map_smul] }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' b a := by
    ext c
    change τ ((b • a)*c)=b • τ (a*c)
    rw [Algebra.smul_mul_assoc,τ.map_smul]

@[simp] theorem frobeniusPairing_apply (τ : R →ₗ[B] B) (a b : R) :
    frobeniusPairing τ a b=τ (a*b) := rfl

variable {M : Type*} [AddCommGroup M] [Module B M] [Module R M]
  [IsScalarTower B R M]

/-- Evaluation against the scalar action, before inversion of the
relative Frobenius pairing. -/
def actionFunctional (l : M →ₗ[B] B) : M →ₗ[B] Module.Dual B R where
  toFun m :=
    { toFun := fun r => l (r • m)
      map_add' r s := by simp [add_smul]
      map_smul' b r := by rw [smul_assoc,l.map_smul]; rfl }
  map_add' m n := by ext r; simp [smul_add]
  map_smul' b m := by
    ext r
    change l (r • (b • m))=b • l (r • m)
    rw [smul_comm,l.map_smul]

@[simp] theorem actionFunctional_apply (l : M →ₗ[B] B) (m : M) (r : R) :
    actionFunctional l m r=l (r • m) := rfl

def frobeniusInverseMap (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) (l : M →ₗ[B] B) :
    M →ₗ[R] R where
  toFun m := (LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm (actionFunctional l m)
  map_add' m n := by simp only [map_add]
  map_smul' a m := by
    apply hτ.injective
    ext r
    have h (m : M) (r : R) :
        τ ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
          (actionFunctional l m)*r)=l (r • m) := by
      exact congrArg (fun f : Module.Dual B R => f r)
        ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).apply_symm_apply
          (actionFunctional l m))
    change τ (_*r)=τ ((a*_)*r)
    rw [h,show (a*(LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
      (actionFunctional l m))*r=
      ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
        (actionFunctional l m))*(r*a) by ring,h]
    rw [mul_smul]

theorem frobeniusInverseMap_spec (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) (l : M →ₗ[B] B)
    (m : M) (r : R) :
    τ (frobeniusInverseMap τ hτ l m*r)=l (r • m) :=
  congrArg (fun f : Module.Dual B R => f r)
    ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).apply_symm_apply
      (actionFunctional l m))

/-- Relative Frobenius adjunction as an actual linear equivalence. -/
def frobeniusDualEquiv (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) :
    (M →ₗ[R] R) ≃ₗ[B] (M →ₗ[B] B) where
  toFun f := τ.comp (f.restrictScalars B)
  invFun := frobeniusInverseMap τ hτ
  left_inv f := by
    apply LinearMap.ext
    intro m
    apply hτ.injective
    ext r
    rw [frobeniusPairing_apply,frobeniusInverseMap_spec]
    change τ (f (r • m))=τ (f m*r)
    rw [f.map_smul]
    congr 1
    exact mul_comm _ _
  right_inv l := by
    apply LinearMap.ext
    intro m
    have h := frobeniusInverseMap_spec τ hτ l m 1
    simpa using h
  map_add' f g := by ext m; simp
  map_smul' b f := by ext m; simp

theorem frobenius_dual_projective (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ))
    [Module.Finite B M] [Module.Projective B M] :
    Module.Projective B (Module.Dual R M) :=
  Module.Projective.of_equiv' (frobeniusDualEquiv (M:=M) τ hτ).symm

theorem frobenius_dual_finite (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ))
    [Module.Finite B M] [Module.Projective B M] :
    Module.Finite B (Module.Dual R M) :=
  Module.Finite.equiv (frobeniusDualEquiv (M:=M) τ hτ).symm

/-- Biduality over the actual algebra follows from finite projectivity
over its coefficient ring and the perfect relative multiplication pairing. -/
theorem frobenius_reflexive (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ))
    [Module.Finite B M] [Module.Projective B M] : Module.IsReflexive R M := by
  let β := frobeniusDualEquiv (M:=M) τ hτ
  let γ := frobeniusDualEquiv (M:=Module.Dual R M) τ hτ
  let δ : M ≃ₗ[B] Module.Dual R (Module.Dual R M) :=
    ((Module.evalEquiv B M).trans β.dualMap).trans γ.symm
  have hδ (m : M) : δ m=Module.Dual.eval R M m := by
    apply γ.injective
    apply LinearMap.ext
    intro f
    change γ (γ.symm (β.dualMap (Module.evalEquiv B M m))) f=
      γ (Module.Dual.eval R M m) f
    rw [γ.apply_symm_apply]
    rfl
  constructor
  have hfun : (Module.Dual.eval R M : M → Module.Dual R (Module.Dual R M))=δ :=
    funext fun m => (hδ m).symm
  rw [hfun]
  exact δ.bijective

section KernelSplitting

variable {X F : Type*} [AddCommGroup X] [Module B X]
  [AddCommGroup F] [Module B F]

/-- A projective quotient gives an explicit retraction of an injective
kernel presentation. It is used over B before relative coinduction. -/
theorem kernel_retraction_of_projective_quotient [Module.Projective B F]
    (i : R →ₗ[B] X) (q : X →ₗ[B] F) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hexact : LinearMap.range i=LinearMap.ker q) :
    ∃ r : X →ₗ[B] R, r.comp i=LinearMap.id := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property q (LinearMap.id : F →ₗ[B] F) hq
  have hqi (a : R) : q (i a)=0 := by
    have ha : i a ∈ LinearMap.ker q := by rw [←hexact]; exact ⟨a,rfl⟩
    exact ha
  let j : R →ₗ[B] LinearMap.ker q := i.codRestrict (LinearMap.ker q) hqi
  have hjinj : Function.Injective j := fun a b h => hi (congrArg Subtype.val h)
  have hjsurj : Function.Surjective j := by
    intro x
    have hx : x.1 ∈ LinearMap.range i := by rw [hexact]; exact x.property
    obtain ⟨a,ha⟩ := hx
    exact ⟨a,Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective j ⟨hjinj,hjsurj⟩
  let p : X →ₗ[B] LinearMap.ker q :=
    (LinearMap.id-s.comp q).codRestrict (LinearMap.ker q) (by
      intro x
      change q (x-s (q x))=0
      have hsx : q (s (q x))=q x := DFunLike.congr_fun hs (q x)
      rw [map_sub,hsx,sub_self])
  refine ⟨e.symm.toLinearMap.comp p,?_⟩
  apply LinearMap.ext
  intro a
  apply e.injective
  change e (e.symm (p (i a)))=e a
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change i a-s (q (i a))=i a
  rw [hqi,map_zero,sub_zero]

end KernelSplitting

section RelativeInjectivity

variable {X F D : Type*} [AddCommGroup X] [Module B X] [Module R X]
  [IsScalarTower B R X] [AddCommGroup F] [Module B F] [Module R F]
  [IsScalarTower B R F] [AddCommGroup D] [Module B D] [Module R D]
  [IsScalarTower B R D]

/-- A coefficient-linear retraction of the regular module becomes an
algebra-linear retraction by the actual Frobenius adjunction. -/
theorem frobenius_retraction (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ))
    (i : R →ₗ[R] X) (r : X →ₗ[B] R)
    (hr : r.comp (i.restrictScalars B)=LinearMap.id) :
    ∃ s : X →ₗ[R] R, s.comp i=LinearMap.id := by
  refine ⟨frobeniusInverseMap τ hτ (τ.comp r),?_⟩
  apply LinearMap.ext
  intro a
  apply hτ.injective
  apply LinearMap.ext
  intro b
  change τ (frobeniusInverseMap τ hτ (τ.comp r) (i a)*b)=τ (a*b)
  rw [frobeniusInverseMap_spec]
  have hri (c : R) : r (i c)=c := DFunLike.congr_fun hr c
  change τ (r (b • i a))=τ (a*b)
  rw [←i.map_smul b a]
  change τ (r (i (b*a)))=τ (a*b)
  rw [hri,mul_comm b a]

/-- The regular algebra is injective against coefficient-split exact
extensions. Projectivity of the quotient supplies the coefficient split. -/
theorem frobenius_extension_retraction (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) [Module.Projective B F]
    (i : R →ₗ[R] X) (q : X →ₗ[R] F) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hexact : LinearMap.range i=LinearMap.ker q) :
    ∃ r : X →ₗ[R] R, r.comp i=LinearMap.id := by
  have hexactB : LinearMap.range (i.restrictScalars B)=
      LinearMap.ker (q.restrictScalars B) := by
    ext x
    exact SetLike.ext_iff.mp hexact x
  obtain ⟨r,hr⟩ := kernel_retraction_of_projective_quotient
    (i.restrictScalars B) (q.restrictScalars B) hi hq hexactB
  exact frobenius_retraction τ hτ i r hr

/-- A retracted actual kernel yields a section of its actual quotient. -/
theorem section_of_kernel_retraction (i : R →ₗ[R] X) (q : X →ₗ[R] F)
    (hq : Function.Surjective q) (hexact : LinearMap.range i=LinearMap.ker q)
    (r : X →ₗ[R] R) (hr : r.comp i=LinearMap.id) :
    ∃ s : F →ₗ[R] X, q.comp s=LinearMap.id := by
  have hqi (a : R) : q (i a)=0 := by
    have ha : i a ∈ LinearMap.ker q := by rw [←hexact]; exact ⟨a,rfl⟩
    exact ha
  have hri (a : R) : r (i a)=a := DFunLike.congr_fun hr a
  let f : LinearMap.ker r →ₗ[R] F := q.comp (LinearMap.ker r).subtype
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hqxy : x.1-y.1 ∈ LinearMap.range i := by
      rw [hexact]
      change q (x.1-y.1)=0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨a,ha⟩ := hqxy
    have har := congrArg r ha
    rw [hri,map_sub,x.property,y.property,sub_self] at har
    apply Subtype.ext
    apply sub_eq_zero.mp
    rw [←ha,har,i.map_zero]
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    refine ⟨⟨x-i (r x),?_⟩,?_⟩
    · change r (x-i (r x))=0
      rw [map_sub,hri,sub_self]
    · change q (x-i (r x))=y
      rw [map_sub,hqi,sub_zero,hx]
  let e := LinearEquiv.ofBijective f ⟨hf_inj,hf_surj⟩
  refine ⟨(LinearMap.ker r).subtype.comp e.symm.toLinearMap,?_⟩
  apply LinearMap.ext
  intro y
  exact e.apply_symm_apply y

omit [Module B D] [IsScalarTower B R D] in
/-- Actual Hom lifting through an extension with regular kernel. This
discharges the `Ext¹(F,R)=0` step of the row argument, rather than taking
it as an unproved axiom or a numeric hypothesis. -/
theorem frobenius_lift (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) [Module.Projective B F]
    (i : R →ₗ[R] X) (q : X →ₗ[R] D) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hexact : LinearMap.range i=LinearMap.ker q)
    (h : F →ₗ[R] D) : ∃ g : F →ₗ[R] X, q.comp g=h := by
  have hqi (a : R) : q (i a)=0 := by
    have ha : i a ∈ LinearMap.ker q := by rw [←hexact]; exact ⟨a,rfl⟩
    exact ha
  let P := mapPullback q h
  let j : R →ₗ[R] P :=
    { toFun := fun a => ⟨(i a,0),by change q (i a)=h 0; rw [hqi,h.map_zero]⟩
      map_add' a b := by apply Subtype.ext; exact Prod.ext (i.map_add a b) (zero_add 0).symm
      map_smul' a b := by apply Subtype.ext; exact Prod.ext (i.map_smul a b) (smul_zero a).symm }
  let p : P →ₗ[R] F := (LinearMap.snd R X F).comp P.subtype
  have hj : Function.Injective j := by
    intro a b hab
    exact hi (congrArg (fun v : P => v.1.1) hab)
  have hp : Function.Surjective p := by
    intro f
    obtain ⟨x,hx⟩ := hq (h f)
    exact ⟨⟨(x,f),hx⟩,rfl⟩
  have hjp : LinearMap.range j=LinearMap.ker p := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      rfl
    · intro hv
      have hv0 : v.1.2=0 := hv
      have hvq : v.1.1 ∈ LinearMap.range i := by
        rw [hexact]
        change q v.1.1=0
        rw [v.property,hv0,h.map_zero]
      obtain ⟨a,ha⟩ := hvq
      exact ⟨a,Subtype.ext (Prod.ext ha hv0.symm)⟩
  obtain ⟨r,hr⟩ := frobenius_extension_retraction τ hτ j p hj hp hjp
  obtain ⟨s,hs⟩ := section_of_kernel_retraction j p hp hjp r hr
  refine ⟨((LinearMap.fst R X F).comp P.subtype).comp s,?_⟩
  apply LinearMap.ext
  intro f
  have hs' : (s f).1.2=f := DFunLike.congr_fun hs f
  change q (s f).1.1=h f
  rw [(s f).property,hs']

end RelativeInjectivity

end Gerstenhaber.DP2.LinearRow
