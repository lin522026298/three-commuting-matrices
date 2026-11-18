import CoordinateChart

noncomputable section
namespace GKGauge
open LinearMap Module Finset Matrix
universe u
variable {F k : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]
def entry (S : Submodule F (Matrix n n F)) (p : n × n) : S →ₗ[F] F where
  toFun z := z.val p.1 p.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- A linear space of matrices meeting GL has an invertible point with
as many chosen, pairwise-distinct entries in the base field as its dimension.
This does not assume the space itself has a model over the base field. -/
theorem gauge_subspace (S : Submodule F (Matrix n n F))
    (h : ∃ z : S, z.val.det ≠ 0) :
    ∃ z : S, z.val.det ≠ 0 ∧ ∃ a : Fin (finrank F S) ↪ n × n,
      ∀ i, z.val (a i).1 (a i).2 ∈ Set.range (algebraMap k F) := by
  classical
  have sep : ∀ v ≠ 0, ∃ i, entry S i v ≠ 0 := by
    intro (v : S) hv
    by_contra! hh
    apply hv; apply Subtype.ext; ext i j
    exact hh (i,j)
  obtain ⟨a,ha,e,he⟩ := exists_chart (entry S) sep
  let κ := Fin (finrank F S)
  let B := Pi.basisFun F κ
  let v : κ → Matrix n n F := fun i => (e.symm (B i)).val
  have hsum (x : κ → F) : ∑ j, x j • v j = (e.symm x).val := by
    have hx := congrArg (fun y => (e.symm y).val) (B.sum_repr x)
    simpa [v,B,Pi.basisFun_repr] using hx
  obtain ⟨z,hz⟩ := h
  have hh : ∃ x : κ → F, (∑ i, x i • v i).det ≠ 0 :=
    ⟨e z, by rw [hsum, e.symm_apply_apply]; exact hz⟩
  obtain ⟨w,hw⟩ := exists_base_invertible (k:=k) v hh
  let w' : κ → F := fun i => algebraMap k F (w i)
  refine ⟨e.symm w', ?_, ⟨a,ha⟩, ?_⟩
  · rwa [← hsum]
  · intro i
    refine ⟨w i, ?_⟩
    have hi := he (e.symm w') i
    rw [e.apply_symm_apply] at hi
    exact hi
end GKGauge
#print axioms GKGauge.gauge_subspace
