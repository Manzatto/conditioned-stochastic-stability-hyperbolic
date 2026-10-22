module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar normalization is independent of the physical norm dictionaries. -/

public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BoundedRateChoice

theorem bounds (pS pH qS qH wS wH floor cutoff : ℝ)
    (hS : qS < pS) (hH : qH < pH) (hc : 0 ≤ cutoff) :
    qS < max (max pS pH) (max wS wH) + 1 ∧
    qH < max (max pS pH) (max wS wH) + 1 ∧
    wS ≤ max (max pS pH) (max wS wH) + 1 ∧
    wH ≤ max (max pS pH) (max wS wH) + 1 ∧
    1 ≤ max floor (max 1 (max pS pH)) + cutoff + 1 ∧
    qS < max floor (max 1 (max pS pH)) + cutoff + 1 ∧
    qH < max floor (max 1 (max pS pH)) + cutoff + 1 := by
  have hPS := le_max_left pS pH
  have hPH := le_max_right pS pH
  have hp := le_max_left (max pS pH) (max wS wH)
  have hw := le_max_right (max pS pH) (max wS wH)
  have hwS := le_max_left wS wH
  have hwH := le_max_right wS wH
  have h1 := le_max_left (1 : ℝ) (max pS pH)
  have hq := le_max_right (1 : ℝ) (max pS pH)
  have hr := le_max_right floor (max 1 (max pS pH))
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

theorem floor_le (floor pressure cutoff : ℝ) (hc : 0 ≤ cutoff) :
    floor ≤ max floor (max 1 pressure) + cutoff + 1 := by
  have h := le_max_left floor (max 1 pressure)
  linarith

theorem pressure_le (pS pH wS wH : ℝ) :
    pS ≤ max (max pS pH) (max wS wH) + 1 ∧
    pH ≤ max (max pS pH) (max wS wH) + 1 := by
  have hs := le_max_left pS pH
  have hh := le_max_right pS pH
  have hw := le_max_left (max pS pH) (max wS wH)
  constructor <;> linarith


/-- All rates are selected by ordinary scalar arithmetic. -/
structure Data (pS pH qS qH wS wH floor cutoff : ℝ) where
  weak : ℝ
  scale : ℝ
  strong_principal : qS < weak
  intermediate_principal : qH < weak
  strong_step : wS ≤ weak
  intermediate_step : wH ≤ weak
  scale_one : 1 ≤ scale
  strong_scale : qS < scale
  intermediate_scale : qH < scale
  cutoff_scale : cutoff ≤ scale
  scale_floor : floor ≤ scale
  pressure_strong : pS ≤ weak
  pressure_intermediate : pH ≤ weak
  scale_formula : scale = max floor (max 1 (max pS pH)) + cutoff + 1

noncomputable def choose (pS pH qS qH wS wH floor cutoff : ℝ)
    (hS : qS < pS) (hH : qH < pH) (hc : 0 ≤ cutoff) :
    Data pS pH qS qH wS wH floor cutoff := by
  have h := bounds pS pH qS qH wS wH floor cutoff hS hH hc
  exact { weak := max (max pS pH) (max wS wH) + 1
          scale := max floor (max 1 (max pS pH)) + cutoff + 1
          strong_principal := h.1
          intermediate_principal := h.2.1
          strong_step := h.2.2.1
          intermediate_step := h.2.2.2.1
          scale_one := h.2.2.2.2.1
          strong_scale := h.2.2.2.2.2.1
          intermediate_scale := h.2.2.2.2.2.2
          cutoff_scale := by
            have h1 := le_max_left (1 : ℝ) (max pS pH)
            have ho := le_max_right floor (max 1 (max pS pH))
            linarith
          scale_floor := floor_le floor (max pS pH) cutoff hc
          pressure_strong := (pressure_le pS pH wS wH).1
          pressure_intermediate := (pressure_le pS pH wS wH).2
          scale_formula := rfl }

end ConditionedStochasticStabilityHyperbolic.Paper.BoundedRateChoice
