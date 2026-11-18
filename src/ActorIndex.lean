import DescendedWords
noncomputable section
namespace DivisorG3
open Module Matrix IsDiscreteValuationRing
variable {V ι : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Fintype ι] [DecidableEq ι]
abbrev wordLattice (P Y Z : Matrix ι ι V) := blockColumns P (box Y Z (Fintype.card ι) (Fintype.card ι))
abbrev actor (P Y Y' Z Z' : Matrix ι ι V) (sy : Y*P=P*Y') (sz : Z*P=P*Z') :=
  Algebra.adjoin V ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _)
set_option backward.isDefEq.respectTransparency false in
theorem actor_ledger (P Y Y' Z Z' C : Matrix ι ι V) (hp : P.det≠0) (sy : Y*P=P*Y')
    (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    length V (colQuot (wordLattice P Y Z)) + length V (actor P Y Y' Z Z' sy sz) =
      Fintype.card ι * length V (QP P) := by
  let A := actor P Y Y' Z Z' sy sz
  let B := box Y Z (Fintype.card ι) (Fintype.card ι)
  have he : length V A.toSubmodule = length V (A.toSubmodule.map (evalAll P)) :=
    LinearEquiv.length_eq (R:=V) (Submodule.equivMapOfInjective (evalAll P) (evalAll_inj P) A.toSubmodule)
  change length V A = length V (A.toSubmodule.map (evalAll P)) at he
  rw [show A.toSubmodule.map (evalAll P)=wordImage P B from box_image_eq _ _ _ _ _ _ sy sz sc] at he
  change length V (colQuot (blockColumns P B)) + length V A = _
  rw [he,
    ←(intrinsic_colength _ _ (block_minor_nonzero P hp B)).1]
  exact block_index P hp B

private theorem ledger_lt (r : ℕ) (hr : 0<r) (h b n : ℕ∞) (hf : n≠⊤) (e : h+b=r*n) :
    n<b ↔ h<(r-1) • n := by
  lift n to ℕ using hf
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hh : h≠⊤ := by intro ht; rw [ht,top_add] at e; exact ENat.natCast_ne_top ((r+1)*n) (by exact_mod_cast e.symm)
  have bh : b≠⊤ := by intro ht; rw [ht,add_top] at e; exact ENat.natCast_ne_top ((r+1)*n) (by exact_mod_cast e.symm)
  lift h to ℕ using hh
  lift b to ℕ using bh
  simp only [Nat.succ_sub_one,nsmul_eq_mul] 
  have en : h+b=(r+1)*n := by exact_mod_cast e
  suffices n<b ↔ h<r*n by exact_mod_cast this
  rw [Nat.add_mul,one_mul] at en
  omega

theorem bad_iff_minor (P Y Y' Z Z' C : Matrix ι ι V) (hp : P.det≠0) (hr : 0<Fintype.card ι)
    (sy : Y*P=P*Y') (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    length V (QP P) < length V (actor P Y Y' Z Z' sy sz) ↔
    ∃ j, addVal V ((wordLattice P Y Z).submatrix id j).det < addVal V (P.det^(Fintype.card ι-1)) := by
  let B := box Y Z (Fintype.card ι) (Fintype.card ι)
  rw [←intrinsic_witness _ _ (block_minor_nonzero P hp B),addVal_pow,←intrinsic_square P hp]
  exact ledger_lt _ hr _ _ _ (Module.length_ne_top_iff.mpr (intrinsic_colength P id (by exact hp)).2)
    (actor_ledger _ _ _ _ _ _ hp sy sz sc)
#print axioms actor_ledger
#print axioms bad_iff_minor
end DivisorG3
