module

public import Gerstenhaber.FourBlocks.RankSpecialization
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Abel

/-!
Finite-dimensional maximum-rank pencils.  These lemmas are pure linear
algebra; they assume no bound for a three-generator action algebra.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap Polynomial

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Place a rectangular map in an actual square endomorphism, without
changing its range dimension. -/
def blockLift (f : V →ₗ[K] W) : Module.End K (V × W) :=
  (LinearMap.inr K V W).comp (f.comp (LinearMap.fst K V W))

@[simp] theorem blockLift_apply (f : V →ₗ[K] W) (v : V) (w : W) :
    blockLift f (v,w) = (0,f v) := rfl

theorem blockLift_add (f g : V →ₗ[K] W) :
    blockLift (f+g) = blockLift f + blockLift g := by
  ext x <;> simp [blockLift]

theorem blockLift_smul (a : K) (f : V →ₗ[K] W) :
    blockLift (a • f) = a • blockLift f := by
  ext x <;> simp [blockLift]

def blockRangeEquiv (f : V →ₗ[K] W) :
    LinearMap.range (blockLift f) ≃ₗ[K] LinearMap.range f where
  toFun y := ⟨y.1.2, by
    obtain ⟨x,hx⟩ := y.2
    exact ⟨x.1, congrArg Prod.snd hx⟩⟩
  invFun y := ⟨(0,y.1), by
    obtain ⟨x,hx⟩ := y.2
    exact ⟨(x,0), by simp [hx]⟩⟩
  left_inv y := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := y.2
    have hz : y.1.1 = 0 := by
      have := congrArg Prod.fst hx
      simpa [blockLift] using this.symm
    exact Prod.ext hz.symm rfl
  right_inv y := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_range_blockLift [FiniteDimensional K W] (f : V →ₗ[K] W) :
    finrank K (LinearMap.range (blockLift f)) = finrank K (LinearMap.range f) :=
  (blockRangeEquiv f).finrank_eq

/-- A uniform rank bound away from zero specializes to a rectangular
linear pencil at zero.  The proof uses the already proved polynomial
minor specialization theorem after the honest square embedding above. -/
theorem finrank_range_pencil_specialize [Infinite K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f g : V →ₗ[K] W) (d : ℕ)
    (hbound : ∀ a : K, a ≠ 0 → finrank K (LinearMap.range (f+a • g)) ≤ d) :
    finrank K (LinearMap.range f) ≤ d := by
  classical
  let b := Module.finBasis K (V × W)
  let A := LinearMap.toMatrix b b (blockLift f)
  let B := LinearMap.toMatrix b b (blockLift g)
  let P := A.map C + (X : K[X]) • B.map C
  have heval (a : K) :
      P.map (evalRingHom a) = LinearMap.toMatrix b b (blockLift (f+a • g)) := by
    rw [blockLift_add, blockLift_smul, map_add, map_smul]
    ext i j
    simp [P,A,B]
    exact mul_comm _ _
  have hrank (h : V →ₗ[K] W) :
      (LinearMap.toMatrix b b (blockLift h)).rank = finrank K (LinearMap.range h) := by
    rw [Matrix.rank_eq_finrank_range_toLin _ b b]
    rw [Matrix.toLin_toMatrix]
    exact finrank_range_blockLift h
  have h := Gerstenhaber.FourBlocks.rank_specialize_le P X X_ne_zero d (by
    intro a ha
    rw [heval,hrank]
    exact hbound a (by simpa using ha)) 0
  simpa only [heval,hrank,zero_smul,add_zero] using h

/-- The genuine maximum-rank pencil lemma.  If adding any scalar
multiple of g cannot raise the rank of f, then g sends the kernel of f
into its range.  No conclusion about a generated algebra is assumed. -/
theorem maximal_rank_pencil_ker_range [Infinite K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f g : V →ₗ[K] W)
    (hmax : ∀ a : K,
      finrank K (LinearMap.range (f+a • g)) ≤ finrank K (LinearMap.range f))
    (v : V) (hv : f v = 0) : g v ∈ LinearMap.range f := by
  classical
  let f' : (V × K) →ₗ[K] W := f.coprod ((LinearMap.id : K →ₗ[K] K).smulRight (g v))
  let g' : (V × K) →ₗ[K] W := g.coprod 0
  have hbound (a : K) (ha : a ≠ 0) :
      finrank K (LinearMap.range (f'+a • g')) ≤ finrank K (LinearMap.range f) := by
    have hinc : LinearMap.range (f'+a • g') ≤ LinearMap.range (f+a • g) := by
      rintro y ⟨x,rfl⟩
      refine ⟨x.1 + (x.2/a) • v, ?_⟩
      have hc : x.2/a * a = x.2 := by field_simp
      simp [f',g',LinearMap.coprod_apply,map_add,map_smul,hv,
        smul_smul,hc,add_comm,add_left_comm,add_assoc]
    exact (Submodule.finrank_mono hinc).trans (hmax a)
  have hdim : finrank K (LinearMap.range f') ≤ finrank K (LinearMap.range f) :=
    finrank_range_pencil_specialize f' g' _ hbound
  have hinc : LinearMap.range f ≤ LinearMap.range f' := by
    rintro y ⟨x,rfl⟩
    exact ⟨(x,0),by simp [f']⟩
  have heq : LinearMap.range f = LinearMap.range f' :=
    Submodule.eq_of_le_of_finrank_le hinc hdim
  rw [heq]
  exact ⟨(0,1),by simp [f']⟩

theorem finrank_finset_sup_le {ι : Type*} [FiniteDimensional K W]
    (s : Finset ι) (p : ι → Submodule K W) :
    finrank K ↥(s.sup p) ≤ ∑ i ∈ s, finrank K (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add_left ih _)

variable {E F : Type*} [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- A maximum-rank slice exists because all slice ranks lie in the
finite interval from zero to the dimension of the actual target. -/
theorem exists_maximal_slice [FiniteDimensional K W]
    (Γ : E →ₗ[K] F →ₗ[K] W) :
    ∃ e0 : E, ∀ e : E,
      finrank K (LinearMap.range (Γ e)) ≤ finrank K (LinearMap.range (Γ e0)) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e : E, finrank K (LinearMap.range (Γ e)) = r
  have h0 : P 0 := ⟨0,by simp⟩
  obtain ⟨e0,he0⟩ := Nat.findGreatest_spec (Nat.zero_le (finrank K W)) h0
  refine ⟨e0,fun e => ?_⟩
  rw [he0]
  exact Nat.le_findGreatest (Submodule.finrank_le _) ⟨e,rfl⟩

/-- Bilinear maximum-image product bound.  Every spanning value is
accounted for by an actual finite sum of slice images. -/
theorem bilinear_slice_finrank_le_product [Infinite K]
    [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K W]
    (Γ : E →ₗ[K] F →ₗ[K] W) (r s : ℕ)
    (hspan : Submodule.span K (Set.range (fun p : E × F => Γ p.1 p.2)) = ⊤)
    (hr : ∀ e : E, finrank K (LinearMap.range (Γ e)) ≤ r)
    (hs : ∀ f : F, finrank K (LinearMap.range (Γ.flip f)) ≤ s) :
    finrank K W ≤ r*s := by
  classical
  obtain ⟨e0,hmax⟩ := exists_maximal_slice Γ
  let f := Γ e0
  let b := Module.finBasis K (LinearMap.range f)
  choose v hv using (fun i => f.surjective_rangeRestrict (b i))
  have hv' (i) : f (v i) = (b i : W) := congrArg Subtype.val (hv i)
  let P : Submodule K W := Finset.univ.sup (fun i => LinearMap.range (Γ.flip (v i)))
  have hvalue (e : E) (i) : Γ e (v i) ∈ P := by
    have hi : LinearMap.range (Γ.flip (v i)) ≤ P := by
      dsimp only [P]
      exact Finset.le_sup (f := fun j => LinearMap.range (Γ.flip (v j))) (Finset.mem_univ i)
    exact hi ⟨e,rfl⟩
  have hfrange : LinearMap.range f ≤ P := by
    intro y hy
    let y' : LinearMap.range f := ⟨y,hy⟩
    have hb : (∑ i, b.repr y' i • (b i : W)) = y := by
      simpa only [map_sum,map_smul,Submodule.subtype_apply] using
        congrArg (LinearMap.range f).subtype (b.sum_repr y')
    rw [← hb]
    apply P.sum_mem
    intro i _
    apply P.smul_mem
    rw [← hv']
    exact hvalue e0 i
  have hall (e : E) (x : F) : Γ e x ∈ P := by
    let y : LinearMap.range f := ⟨f x,⟨x,rfl⟩⟩
    let x0 : F := ∑ i, b.repr y i • v i
    have hfx : f x0 = f x := by
      simp only [x0,map_sum,map_smul,hv']
      simpa only [map_sum,map_smul,Submodule.subtype_apply] using
        congrArg (LinearMap.range f).subtype (b.sum_repr y)
    have hker : f (x-x0) = 0 := by rw [map_sub,hfx,sub_self]
    have hinto : Γ e (x-x0) ∈ LinearMap.range f := by
      apply maximal_rank_pencil_ker_range f (Γ e) _ (x-x0) hker
      intro a
      have h := hmax (e0+a • e)
      rw [map_add,map_smul] at h
      exact h
    have hx0 : Γ e x0 ∈ P := by
      simp only [x0,map_sum,map_smul]
      exact P.sum_mem (fun i _ => P.smul_mem _ (hvalue e i))
    rw [show x = (x-x0)+x0 by abel,map_add]
    exact P.add_mem (hfrange hinto) hx0
  have htop : P = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨e,x⟩,rfl⟩
    exact hall e x
  calc
    finrank K W = finrank K P := by rw [htop,finrank_top]
    _ ≤ ∑ i, finrank K (LinearMap.range (Γ.flip (v i))) :=
      finrank_finset_sup_le Finset.univ _
    _ ≤ ∑ _i : Fin (finrank K (LinearMap.range f)), s :=
      Finset.sum_le_sum (fun i _ => hs (v i))
    _ = finrank K (LinearMap.range f)*s := by simp
    _ ≤ r*s := Nat.mul_le_mul_right s (hr e0)

end Gerstenhaber.FourBlocks.MinimalSource
