module
public import LeanShared.Probability.WeightedRandomMapUniformSmoothing

/-! Arbitrary bounded real control multipliers preserve uniform smoothing,
by their actual positive and negative source-density measures. -/
public noncomputable section
namespace LeanShared.StrongFellerFromUniformDomination
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem continuous_weighted_random_integral
    {X Ω Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [NormalSpace Y]
    [MeasurableSpace Ω] [MeasurableSpace Y] [BorelSpace Y]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (σ : Measure Y) [σ.WeaklyRegular]
    (H : X → Ω → Y) (measurableH : ∀ x, AEMeasurable (H x) ρ)
    (continuousH : ∀ ω, Continuous (fun x => H x ω)) (c : ℝ≥0)
    (bound : ∀ x, ρ.map (H x) ≤ (c : ℝ≥0∞) • σ)
    (w : Ω → ℝ) (measurableW : Measurable w) (B : ℝ≥0) (boundW : ∀ ω, ‖w ω‖ ≤ B)
    {f : Y → ℝ} (integrableF : Integrable f σ) :
    Continuous (fun x => ∫ ω, w ω * f (H x ω) ∂ρ) := by
  let pos : Ω → ℝ≥0 := fun ω => Real.toNNReal (w ω)
  let neg : Ω → ℝ≥0 := fun ω => Real.toNNReal (-w ω)
  have posBound (ω : Ω) : pos ω ≤ B :=
    Real.toNNReal_le_iff_le_coe.mpr ((le_abs_self _).trans (boundW ω))
  have negBound (ω : Ω) : neg ω ≤ B :=
    Real.toNNReal_le_iff_le_coe.mpr ((neg_le_abs _).trans (boundW ω))
  have posMeasurable : Measurable pos := measurableW.real_toNNReal
  have negMeasurable : Measurable neg := measurableW.neg.real_toNNReal
  have positivePart := continuous_nonnegative_weighted_random_integral ρ σ H measurableH
    continuousH c bound pos posMeasurable B posBound integrableF
  have negativePart := continuous_nonnegative_weighted_random_integral ρ σ H measurableH
    continuousH c bound neg negMeasurable B negBound integrableF
  have decomposition (ω : Ω) : (pos ω : ℝ) - (neg ω : ℝ) = w ω := by
    simp only [pos, neg, Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]
  have identity (x : X) :
      (∫ ω, (pos ω : ℝ) * f (H x ω) ∂ρ) - (∫ ω, (neg ω : ℝ) * f (H x ω) ∂ρ) =
        ∫ ω, w ω * f (H x ω) ∂ρ := by
    have integrableActual : Integrable (fun ω => f (H x ω)) ρ :=
      ((integrableF.smul_measure_nnreal).mono_measure (bound x)).comp_aemeasurable (measurableH x)
    have posNorm (ω : Ω) : ‖(pos ω : ℝ)‖ ≤ (B : ℝ) := by
      exact (Real.norm_of_nonneg (pos ω).property).le.trans (posBound ω)
    have negNorm (ω : Ω) : ‖(neg ω : ℝ)‖ ≤ (B : ℝ) := by
      exact (Real.norm_of_nonneg (neg ω).property).le.trans (negBound ω)
    have posIntegrable : Integrable (fun ω => (pos ω : ℝ) * f (H x ω)) ρ :=
      integrableActual.bdd_mul (c := (B : ℝ)) posMeasurable.coe_nnreal_real.aestronglyMeasurable
        (ae_of_all _ posNorm)
    have negIntegrable : Integrable (fun ω => (neg ω : ℝ) * f (H x ω)) ρ :=
      integrableActual.bdd_mul (c := (B : ℝ)) negMeasurable.coe_nnreal_real.aestronglyMeasurable
        (ae_of_all _ negNorm)
    rw [← integral_sub posIntegrable negIntegrable]
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by
      change (pos ω : ℝ) * f (H x ω) - (neg ω : ℝ) * f (H x ω) = w ω * f (H x ω)
      rw [← sub_mul, decomposition])
  convert positivePart.sub negativePart using 1
  funext x
  exact (identity x).symm

end LeanShared.StrongFellerFromUniformDomination
