module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Module

/-! Actual coefficient absorption for a two-generator module. The input is
membership in the ideal error plus the scalar-t image, rather than an
assumed exact relation. The existence of this membership for the intended
head/cotangent map is a separate remaining source bridge. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.SmallHeads

open scoped Pointwise

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

theorem ideal_smul_top_coefficients (J : Ideal S) (u v w : M)
    (hgen : Submodule.span S {u,v} = ⊤)
    (hw : w ∈ J • (⊤ : Submodule S M)) :
    ∃ f ∈ J, ∃ g ∈ J, w = f • u + g • v := by
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro r hr m _
    have hm : m ∈ Submodule.span S {u,v} := by rw [hgen]; trivial
    obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hm
    refine ⟨r*a,J.mul_mem_right a hr,r*b,J.mul_mem_right b hr,?_⟩
    rw [← hab,smul_add,smul_smul,smul_smul]
  · intro x y hx hy
    obtain ⟨a,ha,b,hb,hx⟩ := hx
    obtain ⟨c,hc,d,hd,hy⟩ := hy
    refine ⟨a+c,J.add_mem ha hc,b+d,J.add_mem hb hd,?_⟩
    rw [hx,hy]
    module

def scalarRange (t : S) : Submodule S M :=
  LinearMap.range (t • (LinearMap.id : M →ₗ[S] M))

/-- Both error coefficients and the t-preimage coefficients are obtained
from the actual module membership and its two actual generators. -/
theorem absorb_relation_error (J : Ideal S) (t f0 g0 : S) (u v : M)
    (hgen : Submodule.span S {u,v} = ⊤)
    (he : f0 • u + g0 • v ∈ J • (⊤ : Submodule S M) ⊔ scalarRange t) :
    ∃ f2 ∈ J, ∃ g2 ∈ J, ∃ p q : S,
      (f0-f2-t*p) • u + (g0-g2-t*q) • v = 0 := by
  obtain ⟨x,hx,y,hy,heq⟩ := Submodule.mem_sup.mp he
  obtain ⟨f2,hf2,g2,hg2,hxEq⟩ := ideal_smul_top_coefficients J u v x hgen hx
  obtain ⟨m,hm⟩ := hy
  have hm' : t • m = y := hm
  have hmspan : m ∈ Submodule.span S {u,v} := by rw [hgen]; trivial
  obtain ⟨p,q,hpq⟩ := Submodule.mem_span_pair.mp hmspan
  have hmain : f0 • u + g0 • v = f2 • u + g2 • v + t • (p • u + q • v) := by
    calc
      _ = x+y := heq.symm
      _ = _ := by rw [hxEq,←hm',←hpq]
  refine ⟨f2,hf2,g2,hg2,p,q,?_⟩
  calc
    _ = (f0 • u + g0 • v) - (f2 • u + g2 • v + t • (p • u + q • v)) := by module
    _ = 0 := by rw [hmain,sub_self]

/-- The corrected coefficients retain their literal images in any
quotient killing the prescribed ideal error and t. In the intended use
J is m squared, and the quotient records the two transverse linear parts. -/
theorem absorb_relation_error_preserves_residue
    {A : Type*} [CommRing A] (rho : S →+* A)
    (J : Ideal S) (t f0 g0 : S) (u v : M)
    (hgen : Submodule.span S {u,v} = ⊤)
    (he : f0 • u + g0 • v ∈ J • (⊤ : Submodule S M) ⊔ scalarRange t)
    (hJ : ∀ j ∈ J, rho j = 0) (ht : rho t = 0) :
    ∃ f g : S, f • u + g • v = 0 ∧ rho f = rho f0 ∧ rho g = rho g0 := by
  obtain ⟨f2,hf2,g2,hg2,p,q,hrel⟩ := absorb_relation_error J t f0 g0 u v hgen he
  refine ⟨f0-f2-t*p,g0-g2-t*q,hrel,?_,?_⟩
  · simp [hJ f2 hf2,ht]
  · simp [hJ g2 hg2,ht]

end Gerstenhaber.FourBlocks.SmallHeads
