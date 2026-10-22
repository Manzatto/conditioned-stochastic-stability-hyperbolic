module

public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! The literal bounded control density supplies the genuine real L1 density
used by the weighted strong-Feller approximation argument. No extra density
regularity or integrability hypothesis is added to the paper. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.Laws
variable {ι : Type*} [Fintype ι]

theorem exists_real_integrable_density (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ p : cube (ι := ι) ε → ℝ, Measurable p ∧ (∀ z, 0 ≤ p z) ∧
      Integrable p (cubeVolume ε) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖p z‖ ≤ B) ∧
      L.law ε = (cubeVolume ε).withDensity (fun z => ENNReal.ofReal (p z)) := by
  obtain ⟨q, hq, B, hB, hqB, hrepr⟩ := L.bounded_density ε hε
  have hfinite (z) : q z ≠ ∞ := ne_of_lt ((hqB z).trans_lt (lt_top_iff_ne_top.mpr hB))
  have hint : (∫⁻ z, q z ∂cubeVolume ε) ≠ ∞ := by
    have hmass := congrArg (fun ν : Measure (cube (ι := ι) ε) => ν univ) hrepr
    rw [measure_univ, withDensity_apply q MeasurableSet.univ, Measure.restrict_univ] at hmass
    rw [← hmass]
    exact ENNReal.one_ne_top
  refine ⟨fun z => (q z).toReal, hq.ennreal_toReal, fun z => ENNReal.toReal_nonneg,
    integrable_toReal_of_lintegral_ne_top hq.aemeasurable hint, ?_, ?_⟩
  · refine ⟨B.toReal, ENNReal.toReal_nonneg, fun z => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hB (hqB z)
  · simpa only [ENNReal.ofReal_toReal (hfinite _)] using hrepr

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.Laws
