module

public import Gerstenhaber.FourBlocks.PrimaryDecomposition.Transfer

@[expose] public section

noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition
universe u

def SafeAt (k : Type u) [Field k] (r : ℕ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : Fin 3 → Module.End k W), (∀ i j, Commute (T i) (T j)) →
      IsNilpotent (T 0) → finrank k (T 0).ker = r →
      finrank k (Generated T) ≤ finrank k W

theorem first_failure {k : Type u} [Field k] {s : ℕ} (hf : ¬ SafeAt k s) :
    ∃ r ≤ s, (¬ SafeAt k r) ∧ ∀ j < r, SafeAt k j := by
  classical
  have h : ∃ r, ¬ SafeAt k r := ⟨s,hf⟩
  exact ⟨Nat.find h,Nat.find_min' h hf,Nat.find_spec h,fun j hj => not_not.mp (Nat.find_min h hj)⟩

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem nil_kernel_vector [Nontrivial W] (t : Module.End k W) (ht : IsNilpotent t) :
    ∃ w : W, t w=0 ∧ w≠0 := by
  by_contra! h
  have hker : t.ker = ⊥ := by
    apply bot_unique
    exact fun x hx => (Submodule.mem_bot k).mpr (h x hx)
  obtain ⟨n,hn⟩ := ht
  have hi : Function.Injective ⇑(t^n) := by
    rw [Module.End.coe_pow]; exact (LinearMap.ker_eq_bot.mp hker).iterate n
  obtain ⟨x,hx⟩ := exists_ne (0 : W)
  exact hx (hi (by rw [hn]; rfl))

theorem kernel_strict (t : Module.End k W) (ht : IsNilpotent t)
    (P Q : Submodule k W) (hp : Set.MapsTo t P P) (hq : Set.MapsTo t Q Q)
    (hQ : Q ≠ ⊥) (hd : Disjoint P Q) :
    finrank k (t.restrict hp).ker < finrank k t.ker := by
  let f : (t.restrict hp).ker →ₗ[k] t.ker :=
    (P.subtype.comp (t.restrict hp).ker.subtype).codRestrict _ fun x => congrArg Subtype.val x.2
  have hfi : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : t.ker => z.val) h))
  letI : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
  obtain ⟨q,hqzero,hqne⟩ := nil_kernel_vector (t.restrict hq) (Module.End.isNilpotent.restrict hq ht)
  let v : t.ker := ⟨q.val,congrArg Subtype.val hqzero⟩
  have hns : ¬Function.Surjective f := by
    intro hs
    obtain ⟨x,hx⟩ := hs v
    have hxq : (x.val : W) = q.val := congrArg Subtype.val hx
    exact hqne (Subtype.ext (Submodule.disjoint_def.mp hd _ (hxq ▸ x.val.2) q.2))
  have eqr := LinearMap.finrank_range_of_inj hfi
  have lt := Submodule.finrank_lt_finrank_of_lt
    (lt_top_iff_ne_top.mpr (mt LinearMap.range_eq_top.mp hns))
  rw [finrank_top,eqr] at lt
  exact lt

variable [IsAlgClosed k]

theorem least_bad_joint_top (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeAt k j) :
    ∃ chi : Fin 3 → k, jointSpace T chi = ⊤ := by
  classical
  letI := jointCharactersFintype T hc
  have hex : ∃ c : JointCharacters T, finrank k (jointSpace T c.val) <
      finrank k (Generated (restricted T (jointSpace T c.val) (jointSpace_stable T hc c.val))) := by
    by_contra! he
    have b := generated_finrank_le_sum T (fun c : JointCharacters T => jointSpace T c.val)
      (fun c => jointSpace_stable T hc c.val) (jointCharacters_iSup T hc) he
    rw [sum_finrank_jointSpace T hc] at b
    omega
  obtain ⟨c,bc⟩ := hex
  have uniq (v : JointCharacters T) : c=v := by
    by_contra h
    have hv : c.val ≠ v.val := fun he => h (Subtype.ext he)
    have lt := kernel_strict (T 0) hn (jointSpace T c.val) (jointSpace T v.val)
      (jointSpace_stable T hc c.val 0) (jointSpace_stable T hc v.val 0) v.2
      ((jointSpace_independent T hc).pairwiseDisjoint hv)
    let U := restricted T (jointSpace T c.val) (jointSpace_stable T hc c.val)
    have hn' : IsNilpotent (U 0) := Module.End.isNilpotent.restrict _ hn
    have bs := small _ lt (jointSpace T c.val) U (restricted_commute _ _ _ hc) hn' rfl
    exact (not_lt_of_ge bs) bc
  refine ⟨c.val,top_unique ?_⟩
  rw [←jointCharacters_iSup T hc]
  exact iSup_le fun v => by rw [←uniq v]

theorem least_bad_single_spectrum (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeAt k j) :
    ∃ chi : Fin 3 → k, ∀ i, IsNilpotent (T i-chi i • 1) := by
  obtain ⟨chi,hchi⟩ := least_bad_joint_top T hc hn bad small
  refine ⟨chi,fun i => ?_⟩
  have hs : Set.MapsTo (T i-chi i • (1 : Module.End k W)) (jointSpace T chi) (jointSpace T chi) :=
    fun w h => (jointSpace T chi).sub_mem (jointSpace_stable T hc chi i h) ((jointSpace T chi).smul_mem _ h)
  have hnil : IsNilpotent ((T i-chi i • (1 : Module.End k W)).restrict hs) := by
    have eq : (T i-chi i • (1 : Module.End k W)).restrict hs =
        shifted (restricted T (jointSpace T chi) (jointSpace_stable T hc chi)) chi i := by ext w; rfl
    rw [eq]; exact joint_shift_nilpotent _ hc _ _
  obtain ⟨n,he⟩ := hnil
  refine ⟨n,?_⟩
  ext w
  let v : jointSpace T chi := ⟨w,hchi ▸ Submodule.mem_top⟩
  have hh (j : ℕ) : ((T i - chi i • (1 : Module.End k W)).restrict hs ^ j) v =
      (⟨((T i - chi i • 1)^j) w, by
         change ((T i - chi i • (1 : Module.End k W))^j) v.val ∈ jointSpace T chi
         exact (Submodule.eq_top_iff'.mp hchi) _⟩ : jointSpace T chi) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ',pow_succ',Module.End.mul_apply,ih]; rfl
  have e0 := hh n
  rw [he] at e0
  exact (congrArg Subtype.val e0).symm

#print axioms first_failure
#print axioms least_bad_single_spectrum
end DVRMinimal
