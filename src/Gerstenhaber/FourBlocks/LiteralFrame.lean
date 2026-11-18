module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.Center
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks

/-! Literal three-vector frames for commuting endomorphisms. Over an
algebraically closed field of characteristic zero, independence of the identity
and two commuting endomorphisms forces a frame for the original pair or its
dual. The proof includes the locally dependent chain argument, the quadratic
classification, and the common-image alternative. Matrix corollaries identify
the dual alternative with the ordinary transpose. No dimension estimate or
unproved classification is assumed. -/

open scoped Matrix
open Matrix Module Polynomial

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

def LiteralThreeFrame (U V : Module.End K E) : Prop :=
  ∃ u, LinearIndependent K (![u,U u,V u] : Fin 3 → E)

def LocallyDependentTriple (U V : Module.End K E) : Prop :=
  ∀ u, ¬ LinearIndependent K (![u,U u,V u] : Fin 3 → E)

theorem triple_coefficients_zero {u v w : E}
    (h : LinearIndependent K (![u,v,w] : Fin 3 → E))
    {a b c : K} (hz : a • u+b • v+c • w=0) : a=0 ∧ b=0 ∧ c=0 := by
  have hh := Fintype.linearIndependent_iff.mp h (![a,b,c])
    (by simpa [Fin.sum_univ_succ,add_assoc] using hz)
  exact ⟨hh 0,hh 1,hh 2⟩

theorem chain_three_range_zero (U W : Module.End K E) (u : E)
    (hu : LinearIndependent K (![u,U u,U (U u)] : Fin 3 → E))
    (hcomm : Commute U W)
    (hrange : ∀ z, W z ∈ Submodule.span K {u,U u}) : W=0 := by
  have hline : ∀ z, ∃ a : K, W z=a • u := by
    intro z
    obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp (hrange z)
    obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp (hrange (U z))
    have heq : a • U u+b • U (U u)=c • u+d • U u := by
      calc
        _ = U (a • u+b • U u) := by simp
        _ = U (W z) := congrArg U hab
        _ = W (U z) := LinearMap.congr_fun hcomm.eq z
        _ = _ := hcd.symm
    have hz : (-c) • u+(a-d) • U u+b • U (U u)=0 := by
      calc
        _ = (a • U u+b • U (U u))-(c • u+d • U u) := by module
        _ = 0 := by rw [heq,sub_self]
    have hb := (triple_coefficients_zero hu hz).2.2
    exact ⟨a,by simpa [hb] using hab.symm⟩
  ext z
  obtain ⟨a,ha⟩ := hline z
  obtain ⟨b,hb⟩ := hline (U z)
  have heq : a • U u=b • u := by
    calc
      _ = U (a • u) := by simp
      _ = U (W z) := congrArg U ha.symm
      _ = W (U z) := LinearMap.congr_fun hcomm.eq z
      _ = _ := hb
  have hz : (-b) • u+a • U u+(0:K) • U (U u)=0 := by
    calc
      _ = a • U u-b • u := by module
      _ = 0 := by rw [heq,sub_self]
  have ha0 := (triple_coefficients_zero hu hz).2.1
  simpa [ha0] using ha

theorem alt_three_add_middle (f : E [⋀^Fin 3]→ₗ[K] K) (a b c d : E) :
    f ![a,b+c,d]=f ![a,b,d]+f ![a,c,d] :=
  (f.curryLeft a).map_vecCons_add ![d] b c

theorem alt_three_smul_middle (f : E [⋀^Fin 3]→ₗ[K] K) (a b c : E) (r : K) :
    f ![a,r • b,c]=r * f ![a,b,c] :=
  (f.curryLeft a).map_vecCons_smul ![c] r b

theorem alt_three_add_right (f : E [⋀^Fin 3]→ₗ[K] K) (a b c d : E) :
    f ![a,b,c+d]=f ![a,b,c]+f ![a,b,d] :=
  ((f.curryLeft a).curryLeft b).map_vecCons_add ![] c d

theorem alt_three_smul_right (f : E [⋀^Fin 3]→ₗ[K] K) (a b c : E) (r : K) :
    f ![a,b,r • c]=r * f ![a,b,c] :=
  ((f.curryLeft a).curryLeft b).map_vecCons_smul ![] r c

theorem exists_alternating_three_one {v : Fin 3 → E}
    (hv : LinearIndependent K v) : ∃ f : E [⋀^Fin 3]→ₗ[K] K, f v=1 := by
  let l := Fintype.linearCombination K v
  obtain ⟨g,hg⟩ := l.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  let f : E [⋀^Fin 3]→ₗ[K] K := Matrix.detRowAlternating.compLinearMap g
  refine ⟨f,?_⟩
  have he : ∀ i : Fin 3, g (v i)=Pi.single i (1:K) := by
    intro i
    have h := LinearMap.congr_fun hg (Pi.single i (1:K))
    simpa [l,Fintype.linearCombination_apply_single] using h
  change Matrix.det (fun i : Fin 3 => g (v i))=1
  simp_rw [he]
  have hmat : (fun i : Fin 3 => Pi.single i (1:K))=(1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    simp [Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hmat,Matrix.det_one]

theorem triple_first_pair {u v w : E}
    (h : LinearIndependent K (![u,v,w] : Fin 3 → E)) :
    LinearIndependent K (![u,v] : Fin 2 → E) := by
  have heq : (fun i : Fin 2 => (![u,v,w] : Fin 3 → E) i.castSucc) =
      (![u,v] : Fin 2 → E) := by
    ext i
    fin_cases i <;> rfl
  simpa only [Function.comp_def,heq] using
    h.comp (fun i : Fin 2 => i.castSucc) (Fin.castSucc_injective 2)

theorem dependent_third_mem_span {u v w : E}
    (huv : LinearIndependent K (![u,v] : Fin 2 → E))
    (h : ¬LinearIndependent K (![u,v,w] : Fin 3 → E)) :
    w ∈ Submodule.span K {u,v} := by
  by_contra hm
  have hm' : w ∉ Submodule.span K (Set.range (![u,v] : Fin 2 → E)) := by
    simpa only [Matrix.range_cons_cons_empty] using hm
  apply h
  have heq : Fin.snoc (![u,v] : Fin 2 → E) w = (![u,v,w] : Fin 3 → E) := by
    ext i
    fin_cases i <;> rfl
  simpa only [heq] using huv.finSnoc hm'

theorem mem_span_pair_of_alternating_zero {u v w : E}
    (huv : LinearIndependent K (![u,v] : Fin 2 → E))
    (hzero : ∀ f : E [⋀^Fin 3]→ₗ[K] K, f ![u,v,w]=0) :
    w ∈ Submodule.span K {u,v} := by
  apply dependent_third_mem_span huv
  intro h
  obtain ⟨f,hf⟩ := exists_alternating_three_one h
  exact one_ne_zero (hf.symm.trans (hzero f))

theorem alt_three_add_left (f : E [⋀^Fin 3]→ₗ[K] K) (a b c d : E) :
    f ![a+b,c,d]=f ![a,c,d]+f ![b,c,d] :=
  f.map_vecCons_add ![c,d] a b

theorem alt_three_smul_left (f : E [⋀^Fin 3]→ₗ[K] K) (a b c : E) (r : K) :
    f ![r • a,b,c]=r * f ![a,b,c] :=
  f.map_vecCons_smul ![b,c] r a

@[simp] theorem alt_three_repeat_left (f : E [⋀^Fin 3]→ₗ[K] K) (a b : E) :
    f ![a,b,a]=0 :=
  f.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)

@[simp] theorem alt_three_repeat_right (f : E [⋀^Fin 3]→ₗ[K] K) (a b : E) :
    f ![a,b,b]=0 :=
  f.map_eq_zero_of_eq _ (i := 1) (j := 2) rfl (by decide)

theorem alternating_lld_first_coefficient [CharZero K]
    (U W : Module.End K E) (u z : E) (hWu : W u=0)
    (f : E [⋀^Fin 3]→ₗ[K] K)
    (hzero : ∀ w, f ![w,U w,W w]=0) : f ![u,U u,W z]=0 := by
  have hplus := hzero (u+z)
  have hminus := hzero (u+(-1:K) • z)
  have hz := hzero z
  simp only [map_add,map_neg,hWu,zero_add,neg_one_smul] at hplus hminus
  have hneg : f ![u-z,U u-U z,-W z] =
      -f ![u-z,U u-U z,W z] := by
    simpa only [neg_one_smul,neg_one_mul] using
      alt_three_smul_right f (u-z) (U u-U z) (W z) (-1:K)
  have hminus' : f ![u-z,U u-U z,-W z]=0 := by
    simpa only [sub_eq_add_neg] using hminus
  rw [hneg,neg_eq_zero] at hminus'
  have hsub1 : u-z=u+(-1:K) • z := by module
  have hsub2 : U u-U z=U u+(-1:K) • U z := by module
  rw [hsub1,hsub2] at hminus'
  simp only [alt_three_add_left,alt_three_add_middle,alt_three_smul_left,
    alt_three_smul_middle,neg_one_mul] at hplus hminus'
  rw [hz] at hplus hminus'
  have htwo : (2:K)*f ![u,U u,W z]=0 := by
    linear_combination hplus+hminus'
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The main locally-dependent-chain argument: a commuting third operator
is an affine function of the first as soon as the first has a three-step
cyclic chain. The local-dependence premise is the actual vector predicate. -/
theorem locally_dependent_chain_three_affine [CharZero K]
    (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V) (u : E)
    (hu : LinearIndependent K (![u,U u,U (U u)] : Fin 3 → E)) :
    ∃ a b : K, V=a • LinearMap.id+b • U := by
  have hpair := triple_first_pair hu
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp
    (dependent_third_mem_span hpair (hlld u))
  let W : Module.End K E := V-a • LinearMap.id-b • U
  have hWu : W u=0 := by
    simp only [W,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply]
    rw [← hab]
    module
  have hcommUW : Commute U W := by
    change U*W=W*U
    ext w
    change U (W w)=W (U w)
    simp only [W,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      map_sub,map_smul]
    have hUVw : U (V w)=V (U w) := LinearMap.congr_fun hcomm.eq w
    rw [hUVw]
  have hrange : ∀ z, W z ∈ Submodule.span K {u,U u} := by
    intro z
    apply mem_span_pair_of_alternating_zero hpair
    intro f
    apply alternating_lld_first_coefficient U W u z hWu f
    intro w
    have hz := f.map_linearDependent (![w,U w,V w]) (hlld w)
    have hWw : W w=V w+(-a) • w+(-b) • U w := by
      simp only [W,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply]
      module
    rw [hWw,alt_three_add_right,alt_three_add_right,
      alt_three_smul_right,alt_three_smul_right,
      alt_three_repeat_left,alt_three_repeat_right]
    simpa using hz
  have hW0 := chain_three_range_zero U W u hu hcommUW hrange
  refine ⟨a,b,?_⟩
  apply sub_eq_zero.mp
  calc
    V-(a • LinearMap.id+b • U)=W := by dsimp [W]; module
    _ = 0 := hW0

theorem no_chain_three_of_locally_dependent [CharZero K]
    (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V)
    (hind : LinearIndependent K (![LinearMap.id,U,V] : Fin 3 → Module.End K E)) :
    ∀ u, ¬LinearIndependent K (![u,U u,U (U u)] : Fin 3 → E) := by
  intro u hu
  obtain ⟨a,b,hV⟩ := locally_dependent_chain_three_affine U V hcomm hlld u hu
  have hz : (-a) • (LinearMap.id : Module.End K E)+(-b) • U+(1:K) • V=0 := by
    rw [hV]
    module
  exact one_ne_zero (triple_coefficients_zero hind hz).2.2

/-- A common image line killed by two independent operators gives the
literal frame on the dual vector space. No finite-dimensional or spectral
classification assumption is used here. -/
theorem dual_frame_of_common_image_line
    (A B : Module.End K E) (a : E) (ha : a≠0)
    (hA : ∀ w, A w ∈ Submodule.span K {a})
    (hB : ∀ w, B w ∈ Submodule.span K {a})
    (hAa : A a=0) (hBa : B a=0)
    (hind : LinearIndependent K (![A,B] : Fin 2 → Module.End K E)) :
    LiteralThreeFrame A.dualMap B.dualMap := by
  obtain ⟨h,hh⟩ := Module.Projective.exists_dual_eq_one K ha
  refine ⟨h,Fintype.linearIndependent_iff.mpr ?_⟩
  intro coefficients hzero i
  let α : K := coefficients 0
  let β : K := coefficients 1
  let γ : K := coefficients 2
  have hz : α • h+β • A.dualMap h+γ • B.dualMap h=0 := by
    simpa [α,β,γ,Fin.sum_univ_succ,add_assoc] using hzero
  have hα : α=0 := by
    have he := LinearMap.congr_fun hz a
    simpa [hh,hAa,hBa,LinearMap.dualMap_apply] using he
  have hmap : β • A+γ • B=0 := by
    ext w
    have hmem : (β • A+γ • B) w ∈ Submodule.span K {a} := by
      exact Submodule.add_mem _ (Submodule.smul_mem _ β (hA w))
        (Submodule.smul_mem _ γ (hB w))
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
    have he : h ((β • A+γ • B) w)=0 := by
      have hw := LinearMap.congr_fun hz w
      simpa [hα,LinearMap.dualMap_apply] using hw
    have hc0 : c=0 := by
      rw [← hc,map_smul,hh,smul_eq_mul,mul_one] at he
      exact he
    simpa [hc0] using hc.symm
  have hβγ := hind.eq_zero_of_pair hmap
  fin_cases i
  · exact hα
  · exact hβγ.1
  · exact hβγ.2

theorem exists_alternating_two_one {v : Fin 2 → E}
    (hv : LinearIndependent K v) : ∃ f : E [⋀^Fin 2]→ₗ[K] K, f v=1 := by
  let l := Fintype.linearCombination K v
  obtain ⟨g,hg⟩ := l.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  let f : E [⋀^Fin 2]→ₗ[K] K := Matrix.detRowAlternating.compLinearMap g
  refine ⟨f,?_⟩
  have he : ∀ i : Fin 2, g (v i)=Pi.single i (1:K) := by
    intro i
    have h := LinearMap.congr_fun hg (Pi.single i (1:K))
    simpa [l,Fintype.linearCombination_apply_single] using h
  change Matrix.det (fun i : Fin 2 => g (v i))=1
  simp_rw [he]
  have hmat : (fun i : Fin 2 => Pi.single i (1:K))=(1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hmat,Matrix.det_one]

theorem dependent_pair_mem_span {a b : E} (ha : a≠0)
    (hdep : ¬LinearIndependent K (![a,b] : Fin 2 → E)) :
    b ∈ Submodule.span K {a} := by
  by_contra hm
  apply hdep
  rw [LinearIndependent.pair_iff' ha]
  intro c hc
  exact hm (Submodule.mem_span_singleton.mpr ⟨c,hc⟩)

theorem mem_span_singleton_of_alternating_zero {a b : E} (ha : a≠0)
    (hz : ∀ f : E [⋀^Fin 2]→ₗ[K] K, f ![a,b]=0) :
    b ∈ Submodule.span K {a} := by
  apply dependent_pair_mem_span ha
  intro h
  obtain ⟨f,hf⟩ := exists_alternating_two_one h
  exact one_ne_zero (hf.symm.trans (hz f))

theorem linearMap_exists_apply_ne_zero (A : Module.End K E) (hA : A≠0) :
    ∃ u, A u≠0 := by
  by_contra hnone
  apply hA
  ext u
  by_contra hu
  exact hnone ⟨u,hu⟩

/-- The two-map common-image theorem, for the actual pointwise dependence
predicate. Its proof works over every field, not merely an infinite field. -/
theorem common_image_line_of_pointwise_dependent
    (A B : Module.End K E)
    (hind : LinearIndependent K (![A,B] : Fin 2 → Module.End K E))
    (hdep : ∀ w, ¬LinearIndependent K (![A w,B w] : Fin 2 → E)) :
    ∃ u, A u≠0 ∧ (∀ w, A w ∈ Submodule.span K {A u}) ∧
      (∀ w, B w ∈ Submodule.span K {A u}) := by
  have hAne : A≠0 := by simpa using hind.ne_zero (0 : Fin 2)
  obtain ⟨u,hu⟩ := linearMap_exists_apply_ne_zero A hAne
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    (dependent_pair_mem_span hu (hdep u))
  let W : Module.End K E := B-c • A
  have hWu : W u=0 := by
    simp only [W,LinearMap.sub_apply,LinearMap.smul_apply]
    rw [hc,sub_self]
  have hWne : W≠0 := by
    intro hW0
    have hrel : (-c) • A+(1:K) • B=0 := by
      calc
        _ = W := by dsimp [W]; module
        _ = 0 := hW0
    exact one_ne_zero (hind.eq_zero_of_pair hrel).2
  have hdepW : ∀ w, ¬LinearIndependent K (![A w,W w] : Fin 2 → E) := by
    intro w
    have hWw : W w=(-c) • A w+B w := by
      simp only [W,LinearMap.sub_apply,LinearMap.smul_apply]
      module
    rw [hWw,LinearIndependent.pair_add_smul_right_iff]
    exact hdep w
  have hWline : ∀ w, W w ∈ Submodule.span K {A u} := by
    intro w
    apply mem_span_singleton_of_alternating_zero hu
    intro f
    have hz := f.map_linearDependent (![A w,W w]) (hdepW w)
    have hs := f.map_linearDependent (![A (u+w),W (u+w)]) (hdepW (u+w))
    simp only [map_add,hWu,zero_add,AlternatingMap.map_vecCons_add] at hs
    rw [hz,add_zero] at hs
    exact hs
  obtain ⟨w0,hw0⟩ := linearMap_exists_apply_ne_zero W hWne
  have hAofW : ∀ w, W w≠0 → A w ∈ Submodule.span K {A u} := by
    intro w hw
    have hd : ¬LinearIndependent K (![W w,A w] : Fin 2 → E) := by
      simpa only [LinearIndependent.pair_symm_iff] using hdepW w
    obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp
      (dependent_pair_mem_span hw hd)
    rw [← hd]
    exact Submodule.smul_mem _ d (hWline w)
  have hAline : ∀ w, A w ∈ Submodule.span K {A u} := by
    intro w
    by_cases hw : W w=0
    · have hsum : W (w+w0)≠0 := by simpa [hw] using hw0
      have hm := Submodule.sub_mem _ (hAofW (w+w0) hsum) (hAofW w0 hw0)
      simpa only [map_add,add_sub_cancel_right] using hm
    · exact hAofW w hw
  refine ⟨u,hu,hAline,?_⟩
  intro w
  have heq : B w=W w+c • A w := by
    simp only [W,LinearMap.sub_apply,LinearMap.smul_apply]
    module
  rw [heq]
  exact Submodule.add_mem _ (hWline w) (Submodule.smul_mem _ c (hAline w))

theorem dual_frame_of_pointwise_dependent_square_zero_pair
    (A B : Module.End K E) (hcomm : Commute A B) (hAA : A*A=0)
    (hind : LinearIndependent K (![A,B] : Fin 2 → Module.End K E))
    (hdep : ∀ w, ¬LinearIndependent K (![A w,B w] : Fin 2 → E)) :
    LiteralThreeFrame A.dualMap B.dualMap := by
  obtain ⟨u,hu,hA,hB⟩ := common_image_line_of_pointwise_dependent A B hind hdep
  have hAa : A (A u)=0 := LinearMap.congr_fun hAA u
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hB u)
  have hBa : B (A u)=0 := by
    calc
      _ = A (B u) := (LinearMap.congr_fun hcomm.eq u).symm
      _ = A (c • A u) := congrArg A hc.symm
      _ = 0 := by rw [map_smul,hAa,smul_zero]
  exact dual_frame_of_common_image_line A B (A u) hu hA hB hAa hBa hind

/-- A vector whose polynomial annihilator is the global annihilator turns
local quadratic dependence into an actual global quadratic equation. -/
theorem quadratic_relation_of_no_chain_three [Module.Finite K E]
    (U : Module.End K E)
    (hind : LinearIndependent K
      (![(LinearMap.id : Module.End K E),U] : Fin 2 → Module.End K E))
    (hno : ∀ u, ¬LinearIndependent K (![u,U u,U (U u)] : Fin 3 → E)) :
    ∃ a b : K, U*U=a • LinearMap.id+b • U := by
  classical
  obtain ⟨u,hu⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
    K[X] (Module.AEval' U)
  obtain ⟨u,rfl⟩ := (Module.AEval'.of U).surjective u
  obtain ⟨g,hg,hgn⟩ := Fintype.not_linearIndependent_iff.mp (hno u)
  let a : K := g 0
  let b : K := g 1
  let c : K := g 2
  have hvector : a • u+b • U u+c • U (U u)=0 := by
    simpa [a,b,c,Fin.sum_univ_succ,add_assoc] using hg
  let p : K[X] := Polynomial.C a+Polynomial.C b*Polynomial.X+
    Polynomial.C c*Polynomial.X^2
  have heval : Polynomial.aeval U p=a • LinearMap.id+b • U+c • (U*U) := by
    simp [p,Algebra.algebraMap_eq_smul_one,pow_two]
    rfl
  have hpu : p • Module.AEval'.of U u=0 := by
    change Module.AEval'.of U ((Polynomial.aeval U p) u)=0
    rw [heval]
    simpa using congrArg (Module.AEval'.of U) hvector
  have hpann : p ∈ Module.annihilator K[X] (Module.AEval' U) := by
    rw [← hu]
    exact hpu
  have hpzero : Polynomial.aeval U p=0 := by
    rw [Module.AEval.annihilator_eq_ker_aeval] at hpann
    exact hpann
  have hrel : a • (LinearMap.id : Module.End K E)+b • U+c • (U*U)=0 := by
    rw [← heval]
    exact hpzero
  have hc : c≠0 := by
    intro hc0
    rw [hc0,zero_smul,add_zero] at hrel
    have hab := hind.eq_zero_of_pair hrel
    obtain ⟨i,hi⟩ := hgn
    fin_cases i
    · exact hi hab.1
    · exact hi hab.2
    · exact hi hc0
  have hs := congrArg (fun Z : Module.End K E => c⁻¹ • Z) hrel
  have hs' : (c⁻¹*a) • (LinearMap.id : Module.End K E)+
      (c⁻¹*b) • U+U*U=0 := by
    simpa only [smul_add,smul_smul,inv_mul_cancel₀ hc,one_smul,smul_zero] using hs
  refine ⟨-(c⁻¹*a),-(c⁻¹*b),?_⟩
  apply sub_eq_zero.mp
  calc
    U*U-(-(c⁻¹*a) • LinearMap.id+-(c⁻¹*b) • U) =
        (c⁻¹*a) • LinearMap.id+(c⁻¹*b) • U+U*U := by module
    _ = 0 := hs'

theorem independent_three_scalar_translate {u v w : E}
    (h : LinearIndependent K (![u,v,w] : Fin 3 → E)) (a b : K) :
    LinearIndependent K (![u,a • u+v,b • u+w] : Fin 3 → E) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hg' : g 0 • u+g 1 • (a • u+v)+g 2 • (b • u+w)=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hg
  have hz : (g 0+g 1*a+g 2*b) • u+g 1 • v+g 2 • w=0 := by
    calc
      _ = g 0 • u+g 1 • (a • u+v)+g 2 • (b • u+w) := by module
      _ = 0 := hg'
  obtain ⟨h0,h1,h2⟩ := triple_coefficients_zero h hz
  fin_cases i
  · simpa [h1,h2] using h0
  · exact h1
  · exact h2

theorem frame_of_independent_square_zero_images
    (A B : Module.End K E) (hcomm : Commute A B)
    (hAA : A*A=0) (hBB : B*B=0) (u : E)
    (himages : LinearIndependent K (![A u,B u] : Fin 2 → E)) :
    LinearIndependent K (![u,A u,B u] : Fin 3 → E) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hz : g 0 • u+g 1 • A u+g 2 • B u=0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hg
  have hAv (v : E) : A (A v)=0 := LinearMap.congr_fun hAA v
  have hBv (v : E) : B (B v)=0 := LinearMap.congr_fun hBB v
  have hABA : A (B (A u))=0 := by
    have hc : B (A u)=A (B u) := (LinearMap.congr_fun hcomm.eq u).symm
    rw [hc,hAv]
  have hABB : A (B (B u))=0 := by rw [hBv,map_zero]
  have hAB : g 0 • A (B u)=0 := by
    have ht := congrArg (fun z : E => A (B z)) hz
    simpa [map_add,map_smul,hABA,hABB] using ht
  have h0 : g 0=0 := by
    by_contra hn
    have hABu : A (B u)=0 := (smul_eq_zero.mp hAB).resolve_left hn
    have hAu : g 0 • A u=0 := by
      have ht := congrArg A hz
      simpa [map_add,map_smul,hAv,hABu] using ht
    have hzero : A u=0 := (smul_eq_zero.mp hAu).resolve_left hn
    exact (himages.ne_zero (0 : Fin 2)) hzero
  have hpair : g 1 • A u+g 2 • B u=0 := by simpa [h0] using hz
  have h12 := himages.eq_zero_of_pair hpair
  fin_cases i
  · exact h0
  · exact h12.1
  · exact h12.2

theorem eigen_components_eq_zero
    (U : Module.End K E) (lam mu : K) (hne : lam≠mu) (x y : E)
    (hx : U x=lam • x) (hy : U y=mu • y) (hsum : x+y=0) : x=0 ∧ y=0 := by
  have hd : (lam-mu) • x=0 := by
    calc
      _ = U (x+y)-mu • (x+y) := by rw [map_add,hx,hy]; module
      _ = 0 := by rw [hsum,map_zero,smul_zero,sub_self]
  have hx0 := (smul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨hx0,by simpa [hx0] using hsum⟩

theorem independent_distinct_eigenvectors
    (U : Module.End K E) (lam mu : K) (hne : lam≠mu) (x y : E)
    (hx : U x=lam • x) (hy : U y=mu • y) (hxne : x≠0) (hyne : y≠0) :
    LinearIndependent K (![x,y] : Fin 2 → E) := by
  apply LinearIndependent.pair_iff.mpr
  intro a b hab
  have hax : U (a • x)=lam • (a • x) := by rw [map_smul,hx]; module
  have hby : U (b • y)=mu • (b • y) := by rw [map_smul,hy]; module
  have hz := eigen_components_eq_zero U lam mu hne (a • x) (b • y) hax hby hab
  exact ⟨(smul_eq_zero.mp hz.1).resolve_right hxne,
    (smul_eq_zero.mp hz.2).resolve_right hyne⟩

theorem lld_eigenvector_image_mem_span
    (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V)
    (lam mu : K) (hne : lam≠mu) (x y : E)
    (hx : U x=lam • x) (hy : U y=mu • y) (hxne : x≠0) (hyne : y≠0) :
    V x ∈ Submodule.span K {x} := by
  have hxy := independent_distinct_eigenvectors U lam mu hne x y hx hy hxne hyne
  have hmix : LinearIndependent K (![x+y,lam • x+mu • y] : Fin 2 → E) := by
    simpa only [one_smul,one_mul] using
      (LinearIndependent.pair_add_smul_add_smul_iff (R := K) (S := K)
        (x := x) (y := y) 1 1 lam mu).mpr ⟨hxy,by simpa using hne.symm⟩
  have hw : U (x+y)=lam • x+mu • y := by rw [map_add,hx,hy]
  have hpair : LinearIndependent K (![x+y,U (x+y)] : Fin 2 → E) := by
    rwa [hw]
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp
    (dependent_third_mem_span hpair (hlld (x+y)))
  have hVx : U (V x)=lam • V x := by
    calc
      _ = V (U x) := LinearMap.congr_fun hcomm.eq x
      _ = _ := by rw [hx,map_smul]
  have hVy : U (V y)=mu • V y := by
    calc
      _ = V (U y) := LinearMap.congr_fun hcomm.eq y
      _ = _ := by rw [hy,map_smul]
  have h1 : U (V x-(a+b*lam) • x)=lam • (V x-(a+b*lam) • x) := by
    rw [map_sub,map_smul,hVx,hx]
    module
  have h2 : U (V y-(a+b*mu) • y)=mu • (V y-(a+b*mu) • y) := by
    rw [map_sub,map_smul,hVy,hy]
    module
  have hsum : (V x-(a+b*lam) • x)+(V y-(a+b*mu) • y)=0 := by
    calc
      _ = V (x+y)-(a • (x+y)+b • U (x+y)) := by rw [map_add,hw]; module
      _ = 0 := by rw [hab,sub_self]
  have hz := (eigen_components_eq_zero U lam mu hne _ _ h1 h2 hsum).1
  exact Submodule.mem_span_singleton.mpr ⟨a+b*lam,(sub_eq_zero.mp hz).symm⟩

theorem lld_scalar_on_eigenspace
    (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V) (lam mu : K) (hne : lam≠mu)
    (y : E) (hy : U y=mu • y) (hyne : y≠0) :
    ∃ a : K, ∀ x, U x=lam • x → V x=a • x := by
  let P : Submodule K E := (U-lam • (LinearMap.id : Module.End K E)).ker
  have hP (x : E) : x ∈ P ↔ U x=lam • x := by
    simp only [P,LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.smul_apply,
      LinearMap.id_apply,sub_eq_zero]
  have hpres (x : P) : V x ∈ P := by
    rw [hP]
    have hx := (hP x).mp x.property
    calc
      _ = V (U x) := LinearMap.congr_fun hcomm.eq x
      _ = _ := by rw [hx,map_smul]
  let VP : Module.End K P :=
    { toFun := fun x => ⟨V x,hpres x⟩
      map_add' := fun x z => Subtype.ext (V.map_add x z)
      map_smul' := fun c x => Subtype.ext (V.map_smul c x) }
  have hloc : ∀ x : P, ¬LinearIndependent K (![x,VP x] : Fin 2 → P) := by
    intro x hli
    have hmem : V x ∈ Submodule.span K {(x:E)} := by
      by_cases hx0 : (x:E)=0
      · simp [hx0]
      · exact lld_eigenvector_image_mem_span U V hcomm hlld lam mu hne x y
          ((hP x).mp x.property) hy hx0 hyne
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hrel : c • x+(-1:K) • VP x=0 := by
      apply Subtype.ext
      change c • (x:E)+(-1:K) • V x=0
      rw [hc]
      module
    exact (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) (hli.eq_zero_of_pair hrel).2
  obtain ⟨a,ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hloc
  refine ⟨a,?_⟩
  intro x hx
  have he := LinearMap.congr_fun ha (⟨x,(hP x).mpr hx⟩ : P)
  exact congrArg Subtype.val he

theorem affine_of_distinct_split_quadratic_lld
    (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V)
    (hind : LinearIndependent K
      (![(LinearMap.id : Module.End K E),U] : Fin 2 → Module.End K E))
    (lam mu : K) (hne : lam≠mu)
    (hfactor : (U-lam • (LinearMap.id : Module.End K E))*(U-mu • (LinearMap.id : Module.End K E))=0) :
    ∃ a b : K, V=a • LinearMap.id+b • U := by
  have hneShift (r : K) : U-r • LinearMap.id≠0 := by
    intro h0
    have hrel : (-r) • (LinearMap.id : Module.End K E)+(1:K) • U=0 := by
      calc
        _ = U-r • LinearMap.id := by module
        _ = 0 := h0
    exact one_ne_zero (hind.eq_zero_of_pair hrel).2
  have hswap : (U-mu • (LinearMap.id : Module.End K E))*(U-lam • (LinearMap.id : Module.End K E))=0 := by
    calc
      _ = (U-lam • (LinearMap.id : Module.End K E))*(U-mu • (LinearMap.id : Module.End K E)) := by
        ext z
        change (U-mu • (LinearMap.id : Module.End K E)) ((U-lam • (LinearMap.id : Module.End K E)) z)=
          (U-lam • (LinearMap.id : Module.End K E)) ((U-mu • (LinearMap.id : Module.End K E)) z)
        simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
          map_sub,map_smul]
        module
      _ = 0 := hfactor
  have heigL (z : E) : U ((U-mu • (LinearMap.id : Module.End K E)) z)=
      lam • ((U-mu • (LinearMap.id : Module.End K E)) z) := by
    have h : (U-lam • (LinearMap.id : Module.End K E)) ((U-mu • (LinearMap.id : Module.End K E)) z)=0 :=
      LinearMap.congr_fun hfactor z
    simpa only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      sub_eq_zero] using h
  have heigM (z : E) : U ((U-lam • (LinearMap.id : Module.End K E)) z)=
      mu • ((U-lam • (LinearMap.id : Module.End K E)) z) := by
    have h : (U-mu • (LinearMap.id : Module.End K E)) ((U-lam • (LinearMap.id : Module.End K E)) z)=0 :=
      LinearMap.congr_fun hswap z
    simpa only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      sub_eq_zero] using h
  obtain ⟨zL,hzL⟩ := linearMap_exists_apply_ne_zero (U-mu • (LinearMap.id : Module.End K E)) (hneShift mu)
  obtain ⟨zM,hzM⟩ := linearMap_exists_apply_ne_zero (U-lam • (LinearMap.id : Module.End K E)) (hneShift lam)
  obtain ⟨c,hc⟩ := lld_scalar_on_eigenspace U V hcomm hlld lam mu hne
    ((U-lam • (LinearMap.id : Module.End K E)) zM) (heigM zM) hzM
  obtain ⟨d,hd⟩ := lld_scalar_on_eigenspace U V hcomm hlld mu lam hne.symm
    ((U-mu • (LinearMap.id : Module.End K E)) zL) (heigL zL) hzL
  let b : K := (c-d)/(lam-mu)
  let a : K := c-b*lam
  have hb : b*(lam-mu)=c-d := by
    exact div_mul_cancel₀ (c-d) (sub_ne_zero.mpr hne)
  have haL : a+b*lam=c := by dsimp [a]; ring
  have haM : a+b*mu=d := by
    calc
      _ = c-b*(lam-mu) := by dsimp [a]; ring
      _ = d := by rw [hb]; ring
  refine ⟨a,b,?_⟩
  ext z
  let x : E := (lam-mu)⁻¹ • ((U-mu • (LinearMap.id : Module.End K E)) z)
  let y : E := (-(lam-mu)⁻¹) • ((U-lam • (LinearMap.id : Module.End K E)) z)
  have hx : U x=lam • x := by
    dsimp [x]
    rw [map_smul]
    have he : U (U z-mu • z)=lam • (U z-mu • z) := heigL z
    rw [he]
    module
  have hy : U y=mu • y := by
    dsimp [y]
    rw [map_smul]
    have he : U (U z-lam • z)=mu • (U z-lam • z) := heigM z
    rw [he]
    module
  have hz : z=x+y := by
    symm
    calc
      x+y=((lam-mu)⁻¹*(lam-mu)) • z := by
        dsimp [x,y]
        module
      _ = z := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne),one_smul]
  change V z=a • z+b • U z
  calc
    V z=c • x+d • y := by rw [hz,map_add,hc x hx,hd y hy]
    _ = (a+b*lam) • x+(a+b*mu) • y := by rw [haL,haM]
    _ = a • z+b • U z := by rw [hz,map_add,hx,hy]; module

theorem independent_three_swap_last {u v w : E}
    (h : LinearIndependent K (![u,v,w] : Fin 3 → E)) :
    LinearIndependent K (![u,w,v] : Fin 3 → E) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hz : g 0 • u+g 2 • v+g 1 • w=0 := by
    calc
      _ = g 0 • u+g 1 • w+g 2 • v := by module
      _ = 0 := by simpa [Fin.sum_univ_succ,add_assoc] using hg
  obtain ⟨h0,h2,h1⟩ := triple_coefficients_zero h hz
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem triple_last_pair {u v w : E}
    (h : LinearIndependent K (![u,v,w] : Fin 3 → E)) :
    LinearIndependent K (![v,w] : Fin 2 → E) := by
  have heq : (fun i : Fin 2 => (![u,v,w] : Fin 3 → E) i.succ) =
      (![v,w] : Fin 2 → E) := by
    ext i
    fin_cases i <;> rfl
  simpa only [Function.comp_def,heq] using
    h.comp (fun i : Fin 2 => i.succ) (Fin.succ_injective 2)

theorem scalar_square_zero_of_independent_lld [CharZero K] [IsAlgClosed K]
    [Module.Finite K E] (U V : Module.End K E) (hcomm : Commute U V)
    (hlld : LocallyDependentTriple U V)
    (hind : LinearIndependent K
      (![(LinearMap.id : Module.End K E),U,V] : Fin 3 → Module.End K E)) :
    ∃ lam : K, (U-lam • LinearMap.id)*(U-lam • LinearMap.id)=0 := by
  have hindIU := triple_first_pair hind
  obtain ⟨a,b,hquad⟩ := quadratic_relation_of_no_chain_three U hindIU
    (no_chain_three_of_locally_dependent U V hcomm hlld hind)
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (b^2+4*a) (by decide : 0<2)
  let lam : K := (b+s)/2
  let mu : K := (b-s)/2
  have hsum : lam+mu=b := by dsimp [lam,mu]; ring
  have hprod : lam*mu= -a := by
    dsimp [lam,mu]
    field_simp
    linear_combination -hs
  have hfactor : (U-lam • LinearMap.id)*(U-mu • LinearMap.id)=0 := by
    ext z
    change (U-lam • (LinearMap.id : Module.End K E))
      ((U-mu • (LinearMap.id : Module.End K E)) z)=0
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      map_sub,map_smul]
    have hUz : U (U z)=a • z+b • U z := LinearMap.congr_fun hquad z
    rw [hUz]
    calc
      _ = (a+lam*mu) • z+(b-(lam+mu)) • U z := by module
      _ = 0 := by rw [hsum,hprod]; simp
  by_cases heq : lam=mu
  · exact ⟨lam,by simpa only [heq] using hfactor⟩
  · obtain ⟨c,d,hV⟩ := affine_of_distinct_split_quadratic_lld
      U V hcomm hlld hindIU lam mu heq hfactor
    have hz : (-c) • (LinearMap.id : Module.End K E)+(-d) • U+(1:K) • V=0 := by
      rw [hV]
      module
    exact (one_ne_zero (triple_coefficients_zero hind hz).2.2).elim

/-- The complete literal-frame classification for the actual commuting
operators, with no plane generator automorphism and no hypothesis which
already asserts the desired frame. -/
theorem literal_frame_or_dual_of_commute_independent [CharZero K] [IsAlgClosed K]
    [Module.Finite K E] (U V : Module.End K E) (hcomm : Commute U V)
    (hind : LinearIndependent K
      (![(LinearMap.id : Module.End K E),U,V] : Fin 3 → Module.End K E)) :
    LiteralThreeFrame U V ∨ LiteralThreeFrame U.dualMap V.dualMap := by
  classical
  by_cases hframe : LiteralThreeFrame U V
  · exact Or.inl hframe
  have hlld : LocallyDependentTriple U V := by
    intro u hu
    exact hframe ⟨u,hu⟩
  obtain ⟨α,hAA⟩ := scalar_square_zero_of_independent_lld U V hcomm hlld hind
  have hlldSwap : LocallyDependentTriple V U := by
    intro u hu
    exact hlld u (independent_three_swap_last hu)
  obtain ⟨β,hBB⟩ := scalar_square_zero_of_independent_lld V U hcomm.symm hlldSwap
    (independent_three_swap_last hind)
  let A : Module.End K E := U-α • LinearMap.id
  let B : Module.End K E := V-β • LinearMap.id
  have hcommAB : Commute A B := by
    change A*B=B*A
    ext z
    change A (B z)=B (A z)
    simp only [A,B,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      map_sub,map_smul]
    have hc : U (V z)=V (U z) := LinearMap.congr_fun hcomm.eq z
    rw [hc]
    module
  have hindAB : LinearIndependent K (![A,B] : Fin 2 → Module.End K E) := by
    have hshift := independent_three_scalar_translate hind (-α) (-β)
    have hA : (-α) • (LinearMap.id : Module.End K E)+U=A := by dsimp [A]; module
    have hB : (-β) • (LinearMap.id : Module.End K E)+V=B := by dsimp [B]; module
    rw [hA,hB] at hshift
    exact triple_last_pair hshift
  have hU (u : E) : U u=α • u+A u := by
    simp only [A,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply]
    module
  have hV (u : E) : V u=β • u+B u := by
    simp only [B,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply]
    module
  have hdep : ∀ u, ¬LinearIndependent K (![A u,B u] : Fin 2 → E) := by
    intro u hu
    have hi := frame_of_independent_square_zero_images A B hcommAB hAA hBB u hu
    apply hframe
    refine ⟨u,?_⟩
    rw [hU,hV]
    exact independent_three_scalar_translate hi α β
  obtain ⟨h,hh⟩ := dual_frame_of_pointwise_dependent_square_zero_pair A B hcommAB
    hAA hindAB hdep
  refine Or.inr ⟨h,?_⟩
  have hUd : U.dualMap h=α • h+A.dualMap h := by
    ext z
    simp only [LinearMap.dualMap_apply,LinearMap.add_apply,LinearMap.smul_apply]
    rw [hU,map_add,map_smul]
  have hVd : V.dualMap h=β • h+B.dualMap h := by
    ext z
    simp only [LinearMap.dualMap_apply,LinearMap.add_apply,LinearMap.smul_apply]
    rw [hV,map_add,map_smul]
  rw [hUd,hVd]
  exact independent_three_scalar_translate hh α β

section MatrixCorollaries

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem independent_of_nonscalar_nonaffine {F : Type*} [AddCommGroup F] [Module K F]
    (e u v : F) (he : e≠0) (hu : ¬∃ a : K, u=a • e)
    (hv : ¬∃ a b : K, v=a • u+b • e) :
    LinearIndependent K (![e,u,v] : Fin 3 → F) := by
  have hp : LinearIndependent K (![e,u] : Fin 2 → F) := by
    apply (LinearIndependent.pair_iff' he).mpr
    intro a ha
    exact hu ⟨a,ha.symm⟩
  have hr : Set.range (![e,u] : Fin 2 → F)={e,u} := by
    ext w
    simp only [Set.mem_range,Fin.exists_fin_two,Matrix.cons_val_zero,
      Matrix.cons_val_one,Set.mem_insert_iff,Set.mem_singleton_iff]
    simp only [eq_comm]
  have hnot : v∉Submodule.span K (Set.range (![e,u] : Fin 2 → F)) := by
    intro hmem
    rw [hr] at hmem
    obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hmem
    apply hv
    exact ⟨b,a,by simpa [add_comm] using hab.symm⟩
  have hs := hp.finSnoc hnot
  have htuple : (Fin.snoc (![e,u] : Fin 2 → F) v) = (![e,u,v] : Fin 3 → F) := by
    ext i
    fin_cases i <;> rfl
  rwa [htuple] at hs

theorem matrix_dual_dotProduct (M : Matrix n n K) (v : n → K) :
    (Matrix.toLinAlgEquiv' M).dualMap (dotProductEquiv K n v) =
      dotProductEquiv K n (M.transpose *ᵥ v) := by
  apply LinearMap.ext
  intro w
  change v ⬝ᵥ (M *ᵥ w) = (M.transpose *ᵥ v) ⬝ᵥ w
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem matrix_frame_or_transpose_of_commute_independent
    [CharZero K] [IsAlgClosed K]
    (U V : Matrix n n K) (hcomm : Commute U V)
    (hind : LinearIndependent K (![1,U,V] : Fin 3 → Matrix n n K)) :
    (∃ u : n → K, LinearIndependent K (![u,U *ᵥ u,V *ᵥ u] : Fin 3 → n → K)) ∨
    (∃ u : n → K, LinearIndependent K
      (![u,U.transpose *ᵥ u,V.transpose *ᵥ u] : Fin 3 → n → K)) := by
  let e : Matrix n n K ≃ₐ[K] Module.End K (n → K) := Matrix.toLinAlgEquiv'
  have hi := hind.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have ht : (fun i => e (![1,U,V] i)) =
      (![(LinearMap.id : Module.End K (n → K)),e U,e V] : Fin 3 → _) := by
    ext i
    fin_cases i <;> simp [e]
  change LinearIndependent K (fun i => e (![1,U,V] i)) at hi
  rw [ht] at hi
  have hc : Commute (e U) (e V) := by
    change e U * e V=e V * e U
    calc
      _ = e (U*V) := (map_mul e U V).symm
      _ = e (V*U) := congrArg e hcomm.eq
      _ = _ := map_mul e V U
  rcases literal_frame_or_dual_of_commute_independent (e U) (e V) hc hi with
    h | h
  · obtain ⟨u,hu⟩ := h
    exact Or.inl ⟨u,hu⟩
  · obtain ⟨f,hf⟩ := h
    let d := dotProductEquiv K n
    let u : n → K := d.symm f
    have hh := hf.map' d.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr d.symm.injective)
    have hU : d.symm ((e U).dualMap f)=U.transpose *ᵥ u := by
      apply d.injective
      rw [d.apply_symm_apply]
      change (Matrix.toLinAlgEquiv' U).dualMap f =
        dotProductEquiv K n (U.transpose *ᵥ u)
      rw [← matrix_dual_dotProduct]
      congr 1
      exact (d.apply_symm_apply f).symm
    have hV : d.symm ((e V).dualMap f)=V.transpose *ᵥ u := by
      apply d.injective
      rw [d.apply_symm_apply]
      change (Matrix.toLinAlgEquiv' V).dualMap f =
        dotProductEquiv K n (V.transpose *ᵥ u)
      rw [← matrix_dual_dotProduct]
      congr 1
      exact (d.apply_symm_apply f).symm
    have htuple : (fun i => d.symm (![f,(e U).dualMap f,(e V).dualMap f] i)) =
        (![u,U.transpose *ᵥ u,V.transpose *ᵥ u] : Fin 3 → n → K) := by
      ext i
      fin_cases i
      · rfl
      · exact congrFun hU _
      · exact congrFun hV _
    change LinearIndependent K
      (fun i => d.symm (![f,(e U).dualMap f,(e V).dualMap f] i)) at hh
    rw [htuple] at hh
    exact Or.inr ⟨u,hh⟩

theorem matrix_frame_or_transpose_of_nonscalar_nonaffine
    [CharZero K] [IsAlgClosed K] [Nonempty n]
    (U V : Matrix n n K) (hcomm : Commute U V)
    (hU : ¬∃ a : K, U=a • (1 : Matrix n n K))
    (hV : ¬∃ a b : K, V=a • U+b • (1 : Matrix n n K)) :
    (∃ u : n → K, LinearIndependent K (![u,U *ᵥ u,V *ᵥ u] : Fin 3 → n → K)) ∨
    (∃ u : n → K, LinearIndependent K
      (![u,U.transpose *ᵥ u,V.transpose *ᵥ u] : Fin 3 → n → K)) := by
  apply matrix_frame_or_transpose_of_commute_independent U V hcomm
  exact independent_of_nonscalar_nonaffine (1 : Matrix n n K) U V one_ne_zero hU hV

end MatrixCorollaries

end Gerstenhaber.FourBlocks

#print axioms Gerstenhaber.FourBlocks.locally_dependent_chain_three_affine
#print axioms Gerstenhaber.FourBlocks.no_chain_three_of_locally_dependent
#print axioms Gerstenhaber.FourBlocks.dual_frame_of_common_image_line
#print axioms Gerstenhaber.FourBlocks.common_image_line_of_pointwise_dependent
#print axioms Gerstenhaber.FourBlocks.dual_frame_of_pointwise_dependent_square_zero_pair
#print axioms Gerstenhaber.FourBlocks.quadratic_relation_of_no_chain_three
#print axioms Gerstenhaber.FourBlocks.literal_frame_or_dual_of_commute_independent



#print axioms Gerstenhaber.FourBlocks.matrix_frame_or_transpose_of_commute_independent
#print axioms Gerstenhaber.FourBlocks.matrix_frame_or_transpose_of_nonscalar_nonaffine
