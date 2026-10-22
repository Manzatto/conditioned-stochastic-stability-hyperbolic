module

public import LeanShared.Probability.AnnealedKernelDuality
public import LeanShared.Probability.WeightedConditioning
public import LeanShared.Probability.KernelAdjointDensity

/-! The normalized departure-weighted forward kernel is exactly the actual
noise-weighted random-map construction. Individual Jacobian change of
variables therefore produces its averaged adjoint, with no averaged duality
or spectral assumption. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace LeanShared.DepartureWeightedRandomMap

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Departure weighting commutes with constructing and killing the actual
random-map transition. No positivity or bound on the real weight is needed. -/
theorem normalized_killed (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (w : X → ℝ) (R : ℝ) (hw : Measurable w)
    (F : X × Ω → Y) (hF : Measurable F) (K : Set Y) (hK : MeasurableSet K) :
    WeightedRandomMapKernel.killed ρ (fun z => w z.1 / R) F K hK =
      WeightedConditioning.normalizedKernel (RandomMapKernel.killed ρ F hF K hK) w R hw := by
  apply Kernel.ext
  intro x
  change (WeightedRandomMapKernel.transition ρ (fun z : X × Ω => w z.1 / R) F x).restrict K =
    ENNReal.ofReal (w x / R) • ((ρ.map (fun ω => F (x, ω))).restrict K)
  have hW : Measurable (fun z : X × Ω => w z.1 / R) := (hw.comp measurable_fst).div_const R
  rw [WeightedRandomMapKernel.transition_apply ρ (fun z : X × Ω => w z.1 / R) hW F hF x]
  change ((ρ.withDensity (fun _ => ENNReal.ofReal (w x / R))).map
    (fun ω => F (x, ω))).restrict K = _
  have hFx : Measurable (fun ω => F (x, ω)) := hF.comp measurable_prodMk_left
  rw [withDensity_const, Measure.map_smul (f := fun ω => F (x, ω)) _ hFx.aemeasurable,
    Measure.restrict_smul]

/-- The sole duality source is the scalar change-of-variables identity for
EACH noise map; Tonelli constructs the actual averaged adjoint law. -/
theorem normalized_isAdjoint (σ : Measure X) [SFinite σ]
    (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (w : X → ℝ) (R : ℝ) (hw : Measurable w)
    (Wr : X × Ω → ℝ) (hWr : Measurable Wr)
    (F H : X × Ω → X) (hF : Measurable F) (hH : Measurable H)
    (K : Set X) (hK : MeasurableSet K)
    (hchange : ∀ (f g : X → ℝ≥0∞), Measurable f → Measurable g → ∀ ω : Ω,
      (∫⁻ x, g x * (ENNReal.ofReal (Wr (x, ω)) * K.indicator f (H (x, ω))) ∂σ) =
        ∫⁻ x, f x * (ENNReal.ofReal (w x / R) * K.indicator g (F (x, ω))) ∂σ) :
    KernelAdjointDensity.IsAdjoint
      (WeightedConditioning.normalizedKernel (RandomMapKernel.killed ρ F hF K hK) w R hw)
      (WeightedRandomMapKernel.killed ρ Wr H K hK) σ := by
  rw [← normalized_killed ρ w R hw F hF K hK]
  intro f g hf hg
  exact AnnealedKernelDuality.bilinear_duality σ ρ (fun z => w z.1 / R) Wr
    ((hw.comp measurable_fst).div_const R) hWr F H hF hH K hK f g hf hg
    (hchange f g hf hg)

end LeanShared.DepartureWeightedRandomMap
