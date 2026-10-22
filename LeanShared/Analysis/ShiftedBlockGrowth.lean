module
public import LeanShared.Analysis.SpectralRadiusFromCoefficients
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The shifted block growth of matrix coefficients from the lower integral growth, as a standalone
statement. -/
public noncomputable section
open Filter
open scoped Topology ENNReal
namespace LeanShared.SpectralRadiusFromCoefficients

theorem shifted_block_growth_of_integral_growth
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (T : B →L[ℂ] B) (pairing : B →L[ℂ] ℂ) (seed : B) (P : ℝ)
    (I : ℕ → ℝ≥0∞)
    (coefficient : ∀ n, I (n + 1) = ENNReal.ofReal ‖pairing ((T ^ n) seed)‖)
    (growth : ∀ γ : ℝ, 1 < γ → ∃ N : ℕ, 0 < N ∧
      ∀ ξ : ℝ, 0 < ξ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ v : ℝ, 0 < v ∧
        ∀ p : ℕ, 0 < p → ENNReal.ofReal (v * Real.exp ((N * p : ℕ) * (P - ξ))) ≤
          C * ENNReal.ofReal (γ ^ p) * I (N * p)) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ p : ℕ, 0 < p → Real.exp ((N * p : ℕ) * (P - δ)) ≤
        C * ‖pairing ((T ^ (N * p - 1)) seed)‖ := by
  intro δ hδ
  have halfPositive : 0 < δ / 2 := by positivity
  let γ := Real.exp (δ / 2)
  have hγ : 1 < γ := Real.one_lt_exp_iff.mpr halfPositive
  obtain ⟨N, hN, lower⟩ := growth γ hγ
  obtain ⟨C, finiteC, v, positiveV, bound⟩ := lower (δ / 2) halfPositive
  have positiveC : 0 < C.toReal + 1 := by positivity
  refine ⟨N, hN, (C.toReal + 1) / v, div_pos positiveC positiveV, ?_⟩
  intro p hp
  have positiveLength : 0 < N * p := Nat.mul_pos hN hp
  have integralIdentity : I (N * p) =
      ENNReal.ofReal ‖pairing ((T ^ (N * p - 1)) seed)‖ := by
    simpa only [Nat.sub_add_cancel positiveLength] using coefficient (N * p - 1)
  have raw := bound p hp
  rw [integralIdentity] at raw
  have rawReal : v * Real.exp ((N * p : ℕ) * (P - δ / 2)) ≤
      C.toReal * γ ^ p * ‖pairing ((T ^ (N * p - 1)) seed)‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    convert raw using 1
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (Real.exp_pos _).le _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal finiteC]
  have lengthBound : (p : ℝ) ≤ (N * p : ℕ) := by
    exact_mod_cast (show p ≤ N * p from by
      simpa only [one_mul] using Nat.mul_le_mul_right p (show 1 ≤ N from hN))
  have lossBound : Real.exp ((N * p : ℕ) * (P - δ)) * γ ^ p ≤
      Real.exp ((N * p : ℕ) * (P - δ / 2)) := by
    rw [show γ ^ p = Real.exp ((p : ℝ) * (δ / 2)) from (Real.exp_nat_mul _ _).symm,
      ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have combined : (v * Real.exp ((N * p : ℕ) * (P - δ))) * γ ^ p ≤
      ((C.toReal + 1) * ‖pairing ((T ^ (N * p - 1)) seed)‖) * γ ^ p := by
    calc
      _ ≤ v * Real.exp ((N * p : ℕ) * (P - δ / 2)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left lossBound positiveV.le
      _ ≤ C.toReal * γ ^ p * ‖pairing ((T ^ (N * p - 1)) seed)‖ := rawReal
      _ ≤ _ := by
        have hc : C.toReal ≤ C.toReal + 1 := by linarith
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_right hc
            (mul_nonneg (pow_nonneg (Real.exp_pos (δ / 2)).le p)
              (norm_nonneg (pairing ((T ^ (N * p - 1)) seed))))
  have positiveGamma : 0 < γ ^ p := pow_pos (Real.exp_pos (δ / 2)) p
  have canceled := (mul_le_mul_iff_left₀ positiveGamma).mp combined
  have divided := (le_div_iff₀ positiveV).mpr (by simpa only [mul_comm] using canceled)
  simpa only [div_mul_eq_mul_div, mul_comm] using divided

end LeanShared.SpectralRadiusFromCoefficients
