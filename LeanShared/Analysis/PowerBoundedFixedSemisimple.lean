module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A uniformly power-bounded operator has no nontrivial generalized
fixed vectors.  The proof uses the exact affine orbit of a length-two
Jordan chain and the actual uniform power bound.
-/

public section
namespace LeanShared.PowerBoundedFixedSemisimple
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem generalized_fixed_eq_fixed (T : E →L[ℂ] E) (C : ℝ)
    (powerBound : ∀ n : ℕ, ‖T ^ n‖ ≤ C) (v : E)
    (generalized : (T - 1) ((T - 1) v) = 0) : (T - 1) v = 0 := by
  let w := (T - 1) v
  have fixed : T w = w := by
    change T w - w = 0 at generalized
    exact sub_eq_zero.mp generalized
  have first : T v = v + w := by
    change T v = v + (T v - v)
    abel
  have orbit (n : ℕ) : (T ^ n) v = v + (n : ℂ) • w := by
    induction n with
    | zero => simp only [pow_zero, Nat.cast_zero, zero_smul, add_zero]; rfl
    | succ n induction =>
      rw [pow_succ']
      change T ((T ^ n) v) = _
      rw [induction, map_add, map_smul, first, fixed, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
  have bound (n : ℕ) : (n : ℝ) * ‖w‖ ≤ (C + 1) * ‖v‖ := by
    have difference : (n : ℂ) • w = (T ^ n) v - v := by rw [orbit]; abel
    calc
      _ = ‖(n : ℂ) • w‖ := by rw [norm_smul, Complex.norm_natCast]
      _ = ‖(T ^ n) v - v‖ := by rw [difference]
      _ ≤ ‖(T ^ n) v‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ C * ‖v‖ + ‖v‖ := add_le_add
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (powerBound n) (norm_nonneg v))) le_rfl
      _ = _ := by ring
  by_contra nonzero
  have positive : 0 < ‖w‖ := norm_pos_iff.mpr nonzero
  obtain ⟨n, large⟩ := exists_nat_gt (((C + 1) * ‖v‖) / ‖w‖)
  have growth := (div_lt_iff₀ positive).mp large
  linarith [bound n]

theorem ker_fixed_square (T : E →L[ℂ] E) (C : ℝ)
    (powerBound : ∀ n : ℕ, ‖T ^ n‖ ≤ C) : ((T - 1) ^ 2).ker = (T - 1).ker := by
  apply Submodule.ext
  intro v
  change (((T - 1) ^ 2 : E →L[ℂ] E) v = 0) ↔ (T - 1) v = 0
  rw [pow_two]
  constructor
  · exact generalized_fixed_eq_fixed T C powerBound v
  · intro zero
    change (T - 1) ((T - 1) v) = 0
    rw [zero, map_zero]

theorem ker_fixed_power (T : E →L[ℂ] E) (C : ℝ)
    (powerBound : ∀ n : ℕ, ‖T ^ n‖ ≤ C) (n : ℕ) :
    ((T - 1) ^ (n + 1)).ker = (T - 1).ker := by
  let S : Module.End ℂ E := (T - 1).toLinearMap
  have equality : (S ^ 1).ker = (S ^ (1 + 1)).ker := by
    simpa only [S, ← ContinuousLinearMap.toLinearMap_pow, pow_one] using
      (ker_fixed_square T C powerBound).symm
  have stable := (Module.End.ker_pow_constant equality n).symm
  simpa only [S, ← ContinuousLinearMap.toLinearMap_pow, pow_one, Nat.add_comm 1 n] using stable

end LeanShared.PowerBoundedFixedSemisimple
