module
public import LeanShared.Probability.RandomMapUniformSmoothing
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Bounded fixed control weights preserve the proved uniform smoothing
property. Positive source weights are actual withDensity measures. -/
public noncomputable section
namespace LeanShared.StrongFellerFromUniformDomination
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem continuous_nonnegative_weighted_random_integral
    {X Ω Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [NormalSpace Y]
    [MeasurableSpace Ω] [MeasurableSpace Y] [BorelSpace Y]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (σ : Measure Y) [σ.WeaklyRegular]
    (H : X → Ω → Y) (measurableH : ∀ x, AEMeasurable (H x) ρ)
    (continuousH : ∀ ω, Continuous (fun x => H x ω)) (c : ℝ≥0)
    (bound : ∀ x, ρ.map (H x) ≤ (c : ℝ≥0∞) • σ)
    (w : Ω → ℝ≥0) (measurableW : Measurable w) (B : ℝ≥0) (boundW : ∀ ω, w ω ≤ B)
    {f : Y → ℝ} (integrableF : Integrable f σ) :
    Continuous (fun x => ∫ ω, (w ω : ℝ) * f (H x ω) ∂ρ) := by
  let ρw := ρ.withDensity (fun ω => (w ω : ℝ≥0∞))
  have sourceBound : ρw ≤ (B : ℝ≥0∞) • ρ := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ (fun ω => ENNReal.coe_le_coe.mpr (boundW ω)))
  have : IsFiniteMeasure ((B : ℝ≥0∞) • ρ) := Measure.smul_finite ρ ENNReal.coe_ne_top
  have : IsFiniteMeasure ρw := isFiniteMeasure_of_le _ sourceBound
  have measurableWeighted (x : X) : AEMeasurable (H x) ρw :=
    (measurableH x).mono_ac (withDensity_absolutelyContinuous _ _)
  have weightedBound (x : X) : ρw.map (H x) ≤ ((B * c : ℝ≥0) : ℝ≥0∞) • σ := by
    have mapped := Measure.map_mono_of_aemeasurable sourceBound ((measurableH x).smul_measure B)
    rw [Measure.map_smul (B : ℝ≥0∞) (measurableH x)] at mapped
    exact mapped.trans (by
      simpa only [smul_smul, ENNReal.coe_mul] using
        (smul_le_smul_left (B : ℝ≥0∞) (bound x)))
  have smooth := continuous_random_integral ρw σ H measurableWeighted continuousH
    (B * c) weightedBound integrableF
  simpa only [ρw, integral_withDensity_eq_integral_smul measurableW, NNReal.smul_def,
    smul_eq_mul] using smooth

end LeanShared.StrongFellerFromUniformDomination
