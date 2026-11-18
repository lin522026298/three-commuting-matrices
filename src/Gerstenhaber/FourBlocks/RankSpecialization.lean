module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks

open Polynomial

/-- A polynomial matrix cannot have a larger rank at a special value than
its uniform rank bound away from the zeros of one nonzero polynomial.
The excluded polynomial may vanish at the specialization point. This is
the precise algebraic specialization principle needed by the four-block
deformations; no topology or unproved geometric closure principle is used. -/
theorem rank_specialize_le {K n : Type*} [Field K] [Infinite K]
    [Fintype n] [DecidableEq n] (M : Matrix n n K[X])
    (g : K[X]) (hg : g ≠ 0) (d : ℕ)
    (hbound : ∀ a : K, g.eval a ≠ 0 → (M.map (evalRingHom a)).rank ≤ d)
    (a₀ : K) : (M.map (evalRingHom a₀)).rank ≤ d := by
  classical
  let M₀ := M.map (evalRingHom a₀)
  obtain ⟨P,Q,e,_hP,_hQ,hPQ⟩ := Matrix.exists_rank_normal_form M₀
  let f : Fin M₀.rank → n := fun i => e.symm (Sum.inl i)
  let T : Matrix n n K[X] := P.map C * M * Q.map C
  let N : Matrix (Fin M₀.rank) (Fin M₀.rank) K[X] := T.submatrix f f
  have heval (a : K) :
      N.map (evalRingHom a) = (P * M.map (evalRingHom a) * Q).submatrix f f := by
    change (T.submatrix f f).map (evalRingHom a) = _
    rw [← Matrix.submatrix_map]
    congr 1
    change (evalRingHom a).mapMatrix (P.map C * M * Q.map C) = _
    rw [map_mul, map_mul]
    have hconst (A : Matrix n n K) : (evalRingHom a).mapMatrix (A.map C) = A := by
      ext i j
      simp
    rw [hconst P, hconst Q]
    rfl
  have hN₀ : N.map (evalRingHom a₀) = 1 := by
    rw [heval]
    change (P * M₀ * Q).submatrix f f = 1
    rw [hPQ]
    ext i j
    simp [f, Matrix.submatrix_apply]
  have hp : N.det ≠ 0 := by
    intro hp
    have h0 : N.det.eval a₀ = 0 := by rw [hp, eval_zero]
    change (evalRingHom a₀) N.det = 0 at h0
    rw [(evalRingHom a₀).map_det] at h0
    change (N.map (evalRingHom a₀)).det = 0 at h0
    rw [hN₀, Matrix.det_one] at h0
    exact one_ne_zero h0
  have hprod : N.det * g ≠ 0 := mul_ne_zero hp hg
  have hgood : ∃ a : K, (N.det * g).eval a ≠ 0 := by
    by_contra! h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  obtain ⟨a,ha⟩ := hgood
  rw [eval_mul, mul_ne_zero_iff] at ha
  have hNr : (N.map (evalRingHom a)).rank = M₀.rank := by
    rw [Matrix.rank_of_det_ne_zero, Fintype.card_fin]
    change ((evalRingHom a).mapMatrix N).det ≠ 0
    rw [← (evalRingHom a).map_det]
    simpa using ha.1
  calc
    (M.map (evalRingHom a₀)).rank = (N.map (evalRingHom a)).rank := hNr.symm
    _ = ((P * M.map (evalRingHom a) * Q).submatrix f f).rank := by rw [heval]
    _ ≤ (P * M.map (evalRingHom a) * Q).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ (P * M.map (evalRingHom a)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (M.map (evalRingHom a)).rank := Matrix.rank_mul_le_right _ _
    _ ≤ d := hbound a ha.2

end Gerstenhaber.FourBlocks

#print axioms Gerstenhaber.FourBlocks.rank_specialize_le
