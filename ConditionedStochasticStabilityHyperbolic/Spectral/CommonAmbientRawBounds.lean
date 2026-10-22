module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
import Mathlib.Tactic.Ring

/-! # Raw all-power bounds from the produced normalized KL hypotheses

Multiplication by a positive reference rate rescales both exponential rates
and leaves the weak inclusion and all three constants unchanged.
-/
@[expose] public noncomputable section
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientRawBounds

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem norm_raw_power_apply (P : E →L[ℂ] E) (b : ℝ) (hb : 0 < b)
    (n : ℕ) (x : E) :
    ‖((((b : ℂ) • P) ^ n) : E →L[ℂ] E) x‖ = b ^ n * ‖(P ^ n) x‖ := by
  rw [smul_pow, smul_apply, norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]

theorem norm_weak_raw_power_apply (P : E →L[ℂ] E) (i : E →L[ℂ] W)
    (b : ℝ) (hb : 0 < b) (n : ℕ) (x : E) :
    ‖i (((((b : ℂ) • P) ^ n) : E →L[ℂ] E) x)‖ =
      b ^ n * ‖i ((P ^ n) x)‖ := by
  rw [smul_pow, smul_apply, map_smul, norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]

theorem weak_growth {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (h : KellerLiverani1999.Hypotheses P i) (ε : ℝ≥0) (hε : ε ≤ h.window)
    (b : ℝ) (hb : 0 < b) : ∀ n x,
    ‖i (((((b : ℂ) • P ε) ^ n) : E →L[ℂ] E) x)‖ ≤
      h.weakConstant * (b * h.weakRate) ^ n * ‖i x‖ := by
  intro n x
  rw [norm_weak_raw_power_apply _ _ b hb]
  calc
    _ ≤ b ^ n * (h.weakConstant * h.weakRate ^ n * ‖i x‖) :=
      mul_le_mul_of_nonneg_left (h.weak_growth ε hε n x) (pow_nonneg hb.le n)
    _ = _ := by rw [mul_pow]; ring

theorem twoNorm_growth {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (h : KellerLiverani1999.Hypotheses P i) (ε : ℝ≥0) (hε : ε ≤ h.window)
    (b : ℝ) (hb : 0 < b) : ∀ n x,
    ‖(((((b : ℂ) • P ε) ^ n) : E →L[ℂ] E) x)‖ ≤
      h.strongConstant * (b * h.alpha) ^ n * ‖x‖ +
        h.errorConstant * (b * h.weakRate) ^ n * ‖i x‖ := by
  intro n x
  rw [norm_raw_power_apply _ b hb]
  calc
    _ ≤ b ^ n * (h.strongConstant * h.alpha ^ n * ‖x‖ +
        h.errorConstant * h.weakRate ^ n * ‖i x‖) :=
      mul_le_mul_of_nonneg_left (h.twoNorm_growth ε hε n x) (pow_nonneg hb.le n)
    _ = _ := by rw [mul_pow, mul_pow]; ring

end ConditionedStochasticStabilityHyperbolic.CommonAmbientRawBounds
