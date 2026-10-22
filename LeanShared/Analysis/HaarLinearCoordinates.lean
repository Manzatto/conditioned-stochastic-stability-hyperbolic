module
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-! A linear coordinate change carries Haar volume to a finite scalar multiple
of any prescribed Haar volume in the target coordinates. -/
public noncomputable section
namespace LeanShared.HaarLinearCoordinates
open MeasureTheory
open scoped ENNReal

theorem exists_finite_factor
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (μ : Measure E) (σ : Measure F)
    [μ.IsAddHaarMeasure] [σ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ.map e = c • σ := by
  have : Measure.IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  exact ⟨Measure.addHaarScalarFactor (μ.map e) σ, ENNReal.coe_ne_top,
    Measure.isAddLeftInvariant_eq_smul (μ.map e) σ⟩

end LeanShared.HaarLinearCoordinates
