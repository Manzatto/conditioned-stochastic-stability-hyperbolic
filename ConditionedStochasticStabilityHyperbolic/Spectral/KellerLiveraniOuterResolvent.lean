module

public import LeanShared.Analysis.PowerGrowthResolvent
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
import Mathlib.Tactic.Linarith

/-! The actual KL hypotheses construct a uniform outer resolvent region.
The one-step norm need not be smaller than the spectral argument. -/

public section
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [CompleteSpace E] in
/-- All actual family powers have a strong operator-norm bound at weakRate. -/
theorem Hypotheses.power_norm_le {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (h : Hypotheses P i) (ε : ℝ≥0) (hε : ε ≤ h.window) (n : ℕ) :
    ‖P ε ^ n‖ ≤ (h.strongConstant + h.errorConstant) * h.weakRate ^ n := by
  have hweak0 : 0 ≤ h.weakRate := (h.alpha_pos.trans h.alpha_lt_weakRate).le
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (add_nonneg h.strongConstant_pos.le h.errorConstant_pos.le) (pow_nonneg hweak0 n))
  intro x
  have hmain := h.twoNorm_growth ε hε n x
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ h.alpha_pos.le h.alpha_lt_weakRate.le n) h.strongConstant_pos.le)
    (norm_nonneg x)
  have hsecond := mul_le_mul_of_nonneg_left (h.weak_le_strong x)
    (mul_nonneg h.errorConstant_pos.le (pow_nonneg hweak0 n))
  nlinarith

/-- The original KL family has an actual uniformly controlled resolvent
outside its weak-growth disk, before the inner-annulus perturbation argument. -/
theorem Hypotheses.outer_resolvent {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (h : Hypotheses P i) (ε : ℝ≥0) (hε : ε ≤ h.window)
    (z : ℂ) (hz : h.weakRate < ‖z‖) :
    z ∈ resolventSet ℂ (P ε) ∧
      ‖resolvent (P ε) z‖ ≤ (h.strongConstant + h.errorConstant) / (‖z‖ - h.weakRate) := by
  exact LeanShared.PowerGrowthResolvent.exists_resolvent (P ε)
    (h.strongConstant + h.errorConstant) h.weakRate
    (h.alpha_pos.trans h.alpha_lt_weakRate).le (h.power_norm_le ε hε) z hz

/-- A genuine pointwise spectral bound is a consequence of the KL hypotheses. -/
theorem Hypotheses.norm_mem_spectrum_le_weakRate
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (h : Hypotheses P i) (ε : ℝ≥0) (hε : ε ≤ h.window)
    (z : ℂ) (hz : z ∈ spectrum ℂ (P ε)) : ‖z‖ ≤ h.weakRate := by
  by_contra hn
  exact hz (h.outer_resolvent ε hε z (lt_of_not_ge hn)).1

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
