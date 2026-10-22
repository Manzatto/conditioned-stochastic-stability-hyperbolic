module
public import LeanShared.Probability.StrongFellerFromUniformDomination

/-! Continuous random maps with uniformly dominated transition measures
smooth every reference-integrable scalar observable. -/
public noncomputable section
namespace LeanShared.StrongFellerFromUniformDomination
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem continuous_random_integral
    {X Ω Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [NormalSpace Y]
    [MeasurableSpace Ω] [MeasurableSpace Y] [BorelSpace Y]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (σ : Measure Y) [σ.WeaklyRegular]
    (H : X → Ω → Y) (measurableH : ∀ x, AEMeasurable (H x) ρ)
    (continuousH : ∀ ω, Continuous (fun x => H x ω)) (c : ℝ≥0)
    (bound : ∀ x, ρ.map (H x) ≤ (c : ℝ≥0∞) • σ)
    {f : Y → ℝ} (integrableF : Integrable f σ) :
    Continuous (fun x => ∫ ω, f (H x ω) ∂ρ) := by
  have weakFeller (g : Y →ᵇ ℝ) : Continuous (fun x => ∫ y, g y ∂ρ.map (H x)) := by
    have continuousAverage : Continuous (fun x => ∫ ω, g (H x ω) ∂ρ) := by
      apply continuous_of_dominated (bound := fun _ => ‖g‖)
      · intro x
        exact (g.continuous.measurable.comp_aemeasurable (measurableH x)).aestronglyMeasurable
      · exact fun _ => ae_of_all _ (fun _ => g.norm_coe_le_norm _)
      · exact integrable_const _
      · exact ae_of_all _ (fun ω => g.continuous.comp (continuousH ω))
    have identity (x : X) : (∫ y, g y ∂ρ.map (H x)) = ∫ ω, g (H x ω) ∂ρ :=
      integral_map (measurableH x) g.continuous.aestronglyMeasurable
    simpa only [identity] using continuousAverage
  have smooth := continuous_integral σ (fun x => ρ.map (H x)) c bound weakFeller integrableF
  have identity (x : X) : (∫ y, f y ∂ρ.map (H x)) = ∫ ω, f (H x ω) ∂ρ :=
    integral_map (measurableH x)
      ((integrableF.smul_measure_nnreal).mono_measure (bound x)).aestronglyMeasurable
  simpa only [identity] using smooth

end LeanShared.StrongFellerFromUniformDomination
