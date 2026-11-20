module

public import GKGraphCoordinates

@[expose] public section
noncomputable section
namespace GKGraph
universe u
variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F]
variable (r : ℕ) (φ : ring k r →ₐ[k] F)

def enumParam (s : Finset F) (i : Fin s.card) : F := (s.equivFin.symm i).1
theorem param_field_le (s : Finset F) (c : Fin 2 → F) :
    IntermediateField.adjoin k (s : Set F) ≤ pairField k c (enumParam s) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  apply IntermediateField.subset_adjoin
  refine ⟨Sum.inr (s.equivFin ⟨x,hx⟩),?_⟩
  simp [enumParam]

theorem center_mem {n : ℕ} (u : Fin n → F) (c : Fin 2 → F) (j : Fin 2) :
    c j ∈ pairField k c u := IntermediateField.subset_adjoin _ _ ⟨Sum.inl j,rfl⟩

theorem entries_unshift (L : IntermediateField k F) (M : Mat F r) (a : F) (ha : a ∈ L)
    (hm : ∀ i j, (M - a • 1) i j ∈ L) : ∀ i j, M i j ∈ L := by
  intro i j
  have h : (a • (1 : Mat F r)) i j ∈ L := by
    by_cases e : i=j
    · subst j; simpa [Matrix.one_apply] using ha
    · simp [e]
  exact (sub_add_cancel (M i j) ((a • (1 : Mat F r)) i j)) ▸ L.add_mem (hm i j) h

/-- Genuine finite parameter sets for the two nilpotent pairs after subtracting
the common spectrum. Either set may be empty or smaller than its upper budget. -/
theorem centered_parameter_bound (hr : 2 ≤ r) (c : Fin 2 → F) (s t : Finset F)
    (hs : s.card ≤ r*r-2) (ht : t.card ≤ r*r-2)
    (h0 : reducedMatrices k r φ 0 = 0)
    (h1 : ∀ i j, (reducedMatrices k r φ 1 - c 0 • 1) i j ∈ IntermediateField.adjoin k (s : Set F))
    (h2 : ∀ i j, (reducedMatrices k r φ 2 - c 1 • 1) i j ∈ IntermediateField.adjoin k (s : Set F))
    (h3 : ∀ i j, (reducedMatrices k r φ 3 - c 0 • 1) i j ∈ IntermediateField.adjoin k (t : Set F))
    (h4 : ∀ i j, (reducedMatrices k r φ 4 - c 1 • 1) i j ∈ IntermediateField.adjoin k (t : Set F)) :
    Algebra.trdeg k (residueCoordinates k r φ) ≤ (3*r*r-2 : ℕ) := by
  have h := joint_coordinate_budget k r φ c (enumParam s) (enumParam t) h0
    (entries_unshift k r _ _ _ (center_mem k (enumParam s) c 0)
      (fun i j => param_field_le k s c (h1 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam s) c 1)
      (fun i j => param_field_le k s c (h2 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam t) c 0)
      (fun i j => param_field_le k t c (h3 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam t) c 1)
      (fun i j => param_field_le k t c (h4 i j)))
  apply h.trans
  exact_mod_cast (show 2+s.card+t.card+r*r ≤ 3*r*r-2 by
    have hrr : 2 ≤ r*r := (by omega : 2 ≤ 2*2).trans (Nat.mul_le_mul hr hr)
    rw [Nat.mul_assoc]; omega)

/-- Passing to a larger residue field for Jordan/eigenvalue witnesses does not alter
the coordinate transcendence degree, including when the extension is transcendental. -/
theorem coords_map {F' : Type u} [Field F'] [Algebra k F'] (ι : F →ₐ[k] F') :
    (residueCoordinates k r φ).map ι = residueCoordinates k r (ι.comp φ) := by
  unfold residueCoordinates
  rw [IntermediateField.adjoin_map, ←Set.range_comp]; rfl

theorem coords_trdeg_map {F' : Type u} [Field F'] [Algebra k F'] (ι : F →ₐ[k] F') :
    Algebra.trdeg k (residueCoordinates k r φ) =
      Algebra.trdeg k (residueCoordinates k r (ι.comp φ)) := by
  rw [← coords_map]
  exact ((residueCoordinates k r φ).equivMap ι).trdeg_eq

end GKGraph
