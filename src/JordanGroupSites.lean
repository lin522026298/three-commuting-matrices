import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Rev
noncomputable section
namespace ActualJordan
abbrev GroupIx {H : ℕ} (m : Fin H → ℕ) := (h : Fin H) × ((_p : Fin (h.val+1)) × Fin (m h))
variable {d : ℕ} (s : Fin d → ℕ)
def height := ∑ i, s i
abbrev Fiber (h : Fin (height s)) := {i : Fin d // s i=h.val+1}
def multiplicity (h : Fin (height s)) := Fintype.card (Fiber s h)
def pick (h : Fin (height s)) (a : Fin (multiplicity s h)) : Fiber s h :=
  (Fintype.equivFin (Fiber s h)).symm a
abbrev Uix := (i : Fin d) × Fin (s i)
def toPowerIx : GroupIx (multiplicity s) → Uix s :=
  fun ⟨h,p,a⟩ => ⟨(pick s h a).val, Fin.cast (pick s h a).2.symm p.rev⟩
theorem toPower_inj : Function.Injective (toPowerIx s) := by
  rintro ⟨h,p,a⟩ ⟨l,q,b⟩ he
  have hi : (pick s h a).val = (pick s l b).val := congrArg Sigma.fst he
  have hil := congrArg s hi
  rw [(pick s h a).2,(pick s l b).2] at hil
  have hhl : h=l := Fin.ext (by omega)
  subst l
  have hab : a=b := (Fintype.equivFin (Fiber s h)).symm.injective (Subtype.ext hi)
  subst b
  have hpq : p.rev.val = q.rev.val := congrArg (fun x : Uix s => x.2.val) he
  have : p = q := Fin.rev_injective (Fin.ext hpq)
  subst q; rfl

private theorem cast_h {n k : ℕ} (e : n=k) (i : Fin n) : HEq (Fin.cast e i) i := by cases e; rfl

theorem powerIx_surj : Function.Surjective (toPowerIx s) := by
  rintro ⟨i,j⟩
  have hs : 0 < s i := Nat.zero_lt_of_lt j.isLt
  have hmax := Finset.single_le_sum (s:=Finset.univ)
    (f:=s) (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
  let h : Fin (height s) := ⟨s i-1,by unfold height; omega⟩
  have hh : s i = h.val+1 := by dsimp [h]; omega
  let a := (Fintype.equivFin (Fiber s h)) ⟨i,hh⟩
  let p := (Fin.cast hh j).rev
  have ha : pick s h a = ⟨i,hh⟩ := (Fintype.equivFin (Fiber s h)).symm_apply_apply _
  refine ⟨⟨h,p,a⟩,?_⟩
  unfold toPowerIx
  simp [ha,p]
  exact cast_h _ _
def powerEquiv : GroupIx (multiplicity s) ≃ Uix s :=
  Equiv.ofBijective _ ⟨toPower_inj s,powerIx_surj s⟩
end ActualJordan
