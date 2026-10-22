module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLWeightBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A fixed positive envelope for the actual cutoff weight is chosen from
HL positivity on the compact core. Its logarithm changes by at most the
requested tolerance there. Positivity of the original weight away from the
core is not assumed. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

include h in
theorem exists_positive_envelope (w : M → ℝ) (hw : Continuous w)
    (hwn : ∀ x, 0 ≤ w x) (hagrees : EqOn w g Λ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ Continuous (fun x => w x + ε) ∧
      (∀ x, 0 < w x + ε) ∧
      ∀ x ∈ Λ, 0 ≤ Real.log (w x + ε) - Real.log (g x) ∧
        Real.log (w x + ε) - Real.log (g x) ≤ δ := by
  obtain ⟨x₀, hx₀, hminimum⟩ := h.compact_core.exists_isMinOn h.nonempty_core
    h.weight_continuous.continuousOn
  let c := g x₀
  have hc : 0 < c := h.weight_positive x₀ hx₀
  have hmin : ∀ x ∈ Λ, c ≤ g x := hminimum
  let ε := c * (Real.exp δ - 1)
  have hexp : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have hε : 0 < ε := mul_pos hc (sub_pos.mpr hexp)
  refine ⟨ε, hε, hw.add continuous_const, fun x => add_pos_of_nonneg_of_pos (hwn x) hε, ?_⟩
  intro x hx
  have hg : 0 < g x := h.weight_positive x hx
  have hlow : g x ≤ w x + ε := by rw [hagrees hx]; linarith
  have hupp : w x + ε ≤ Real.exp δ * g x := by
    rw [hagrees hx]
    have hprod := mul_le_mul_of_nonneg_right (hmin x hx) (sub_nonneg.mpr hexp.le)
    dsimp [ε]
    nlinarith
  have hlo := Real.log_le_log hg hlow
  have hhi := Real.log_le_log (add_pos_of_nonneg_of_pos (hwn x) hε) hupp
  rw [Real.log_mul (Real.exp_ne_zero δ) hg.ne', Real.log_exp] at hhi
  constructor <;> linarith

end ConditionedStochasticStabilityHyperbolic.Paper.HL
