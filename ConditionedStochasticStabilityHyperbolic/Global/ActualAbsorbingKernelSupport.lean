module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise
public import LeanShared.Dynamics.RobustFiltration

/-! # Actual fixed-A kernel support, including its strictly trapping zero level

A has zero target mass by construction. Under the explicitly strengthened
strict trapping hypothesis, one positive map tolerance also prevents noise
from departing A, uniformly over noise laws. No volume-null boundary is used.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualAbsorbingKernelSupport
open LeanShared.RandomMapKernel LeanShared.WeightedConditioning
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- The actual process killed on A has no one-step target mass in A. -/
theorem target_absorbing_mass_zero
    (noise : Measure Ω) [IsProbabilityMeasure noise] (F : X × Ω → X) (hF : Measurable F)
    (A : Set X) (hA : MeasurableSet A) (w : X → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (x : X) :
    (NoiseKernel.chain noise F hF Aᶜ hA.compl w hw R hR hwR).killedTransition x A = 0 := by
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.smul_apply, smul_eq_mul]
  change _ * ((transition noise F hF x).restrict Aᶜ) A = 0
  rw [Measure.restrict_apply hA]
  simp only [inter_compl_self, measure_empty, mul_zero]

/-- A noisy map preserving A cannot generate a surviving step from A. -/
theorem no_surviving_departure_of_absorbing_invariant
    (noise : Measure Ω) [IsProbabilityMeasure noise] (F : X × Ω → X) (hF : Measurable F)
    (A : Set X) (hA : MeasurableSet A) (w : X → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hinvariant : ∀ x ∈ A, ∀ ω, F (x, ω) ∈ A) (x : X) (hx : x ∈ A) :
    (NoiseKernel.chain noise F hF Aᶜ hA.compl w hw R hR hwR).killedTransition x Aᶜ = 0 := by
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.smul_apply, smul_eq_mul]
  change _ * ((transition noise F hF x).restrict Aᶜ) Aᶜ = 0
  rw [Measure.restrict_apply hA.compl, inter_self, transition_apply]
  rw [Measure.map_apply (show Measurable (fun ω => F (x, ω)) from hF.comp measurable_prodMk_left) hA.compl]
  have he : (fun ω => F (x, ω)) ⁻¹' Aᶜ = ∅ := by
    ext ω
    exact ⟨fun h => False.elim (h (hinvariant x hx ω)), False.elim⟩
  rw [he, measure_empty, mul_zero]

section Strict
variable [MetricSpace X] [CompactSpace X]

omit [MeasurableSpace X] in
/-- Strict deterministic trapping supplies one map tolerance preserving A;
only this explicit strengthened hypothesis is used at the zero level. -/
theorem exists_pos_uniform_absorbing_map_tolerance
    (T : X → X) (hT : Continuous T) (A : Set X) (hA : IsOpen A)
    (hstrict : MapsTo T (closure A) A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
      (∀ x ∈ closure A, dist (F x) (T x) < δ) → MapsTo F A A := by
  obtain ⟨δ, hδ, hthick⟩ := (isClosed_closure.isCompact.image hT).exists_thickening_subset_open
    hA hstrict.image_subset
  refine ⟨δ, hδ, ?_⟩
  intro F hF x hx
  exact hthick (mem_thickening_iff.mpr ⟨T x, ⟨x, subset_closure hx, rfl⟩,
    hF x (subset_closure hx)⟩)

end Strict
end ConditionedStochasticStabilityHyperbolic.Global.ActualAbsorbingKernelSupport
