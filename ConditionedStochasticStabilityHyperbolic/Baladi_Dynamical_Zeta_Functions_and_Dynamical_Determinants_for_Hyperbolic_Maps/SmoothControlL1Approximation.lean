module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Ordinary smooth control-density approximants are constructed from
Mathlib's Lp smooth density theorem; their L1 error tends to zero. -/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace ConditionedStochasticStabilityHyperbolic.SmoothControlL1Approximation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_approximation (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (p : E → ℝ) (hp : Integrable p μ) :
    ∃ pn : ℕ → E → ℝ, (∀ n, HasCompactSupport (pn n) ∧ ContDiff ℝ ∞ (pn n) ∧ Integrable (pn n) μ) ∧
      Tendsto (fun n => ∫ z, ‖p z - pn n z‖ ∂μ) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ g : E → ℝ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (p - g) 1 μ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    MemLp.exist_eLpNorm_sub_le (by simp) le_rfl (memLp_one_iff_integrable.mpr hp) (by positivity)
  choose pn hs hc he using hex
  have hi (n : ℕ) : Integrable (pn n) μ :=
    (hc n).continuous.integrable_of_hasCompactSupport (hs n)
  refine ⟨pn, fun n => ⟨hs n, hc n, hi n⟩, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun _ => norm_nonneg _)) _
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  have hsub := hp.sub (hi n)
  have hnorm : (∫ z, ‖p z - pn n z‖ ∂μ) = (eLpNorm (p - pn n) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hsub.aestronglyMeasurable]
    exact integral_norm_eq_lintegral_enorm hsub.aestronglyMeasurable
  rw [hnorm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (he n)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end ConditionedStochasticStabilityHyperbolic.SmoothControlL1Approximation
