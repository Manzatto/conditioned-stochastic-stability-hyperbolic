module

public import LeanShared.Probability.WeightedRandomMapKernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Nonnegative integrals for actual noise-weighted random maps

These identities retain the state/noise weight and the exact live indicator.
They support Tonelli and change-of-variables arguments for the inverse
transfer without assuming an endpoint density.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LeanShared.WeightedRandomMapKernel

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsFiniteMeasure ρ] (W : X × Ω → ℝ) (hW : Measurable W)

include hW in
theorem lintegral_transition (F : X × Ω → Y) (hF : Measurable F)
    (f : Y → ℝ≥0∞) (hf : Measurable f) (x : X) :
    (∫⁻ y, f y ∂transition ρ W F x) =
      ∫⁻ ω, ENNReal.ofReal (W (x, ω)) * f (F (x, ω)) ∂ρ := by
  have hFx : Measurable (fun ω => F (x, ω)) := hF.comp measurable_prodMk_left
  have hWx : Measurable (fun ω => W (x, ω)) := hW.comp measurable_prodMk_left
  rw [transition_apply ρ W hW F hF x, lintegral_map hf hFx]
  exact lintegral_withDensity_eq_lintegral_mul ρ hWx.ennreal_ofReal
    (show Measurable (fun ω => f (F (x, ω))) from hf.comp hFx)

include hW in
theorem lintegral_killed (F : X × Ω → Y) (hF : Measurable F)
    (K : Set Y) (hK : MeasurableSet K) (f : Y → ℝ≥0∞) (hf : Measurable f) (x : X) :
    (∫⁻ y, f y ∂killed ρ W F K hK x) =
      ∫⁻ ω, ENNReal.ofReal (W (x, ω)) * K.indicator f (F (x, ω)) ∂ρ := by
  change (∫⁻ y, f y ∂(transition ρ W F x).restrict K) = _
  rw [← lintegral_indicator hK]
  exact lintegral_transition ρ W hW F hF _ (hf.indicator hK) x

end LeanShared.WeightedRandomMapKernel
