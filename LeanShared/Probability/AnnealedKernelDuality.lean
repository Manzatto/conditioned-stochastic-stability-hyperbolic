module

public import LeanShared.Probability.WeightedRandomMapIntegrals
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Averaged duality from individual change of variables

The forward and inverse kernels are the actual parameter-weighted killed
random-map kernels. A classical change-of-variables identity for each noise
parameter is integrated using Tonelli. The forward right eigenfunction then
becomes the left eigenmeasure density for the inverse kernel. No averaged
duality or inverse eigenmeasure equation is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LeanShared.AnnealedKernelDuality

open WeightedRandomMapKernel

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  (σ : Measure X) [SFinite σ] (ρ : Measure Ω) [IsFiniteMeasure ρ]
  (Wf Wr : X × Ω → ℝ) (hWf : Measurable Wf) (hWr : Measurable Wr)
  (F H : X × Ω → X) (hF : Measurable F) (hH : Measurable H)
  (K : Set X) (hK : MeasurableSet K)

include hWf hWr hF hH in
/-- A per-map Jacobian identity yields duality for the actual averaged kernels. -/
theorem bilinear_duality (f g : X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hchange : ∀ ω : Ω,
      (∫⁻ x, g x * (ENNReal.ofReal (Wr (x, ω)) * K.indicator f (H (x, ω))) ∂σ) =
        ∫⁻ x, f x * (ENNReal.ofReal (Wf (x, ω)) * K.indicator g (F (x, ω))) ∂σ) :
    (∫⁻ x, g x * (∫⁻ y, f y ∂killed ρ Wr H K hK x) ∂σ) =
      ∫⁻ x, f x * (∫⁻ y, g y ∂killed ρ Wf F K hK x) ∂σ := by
  have hrmeas : Measurable (fun p : X × Ω =>
      g p.1 * (ENNReal.ofReal (Wr p) * K.indicator f (H p))) :=
    (hg.comp measurable_fst).mul (hWr.ennreal_ofReal.mul ((hf.indicator hK).comp hH))
  have hfmeas : Measurable (fun p : X × Ω =>
      f p.1 * (ENNReal.ofReal (Wf p) * K.indicator g (F p))) :=
    (hf.comp measurable_fst).mul (hWf.ennreal_ofReal.mul ((hg.indicator hK).comp hF))
  have hright (x : X) : Measurable (fun ω => ENNReal.ofReal (Wr (x, ω)) *
      K.indicator f (H (x, ω))) :=
    (hWr.comp measurable_prodMk_left).ennreal_ofReal.mul
      ((hf.indicator hK).comp (hH.comp measurable_prodMk_left))
  have hforward (x : X) : Measurable (fun ω => ENNReal.ofReal (Wf (x, ω)) *
      K.indicator g (F (x, ω))) :=
    (hWf.comp measurable_prodMk_left).ennreal_ofReal.mul
      ((hg.indicator hK).comp (hF.comp measurable_prodMk_left))
  simp_rw [lintegral_killed ρ Wr hWr H hH K hK f hf,
    lintegral_killed ρ Wf hWf F hF K hK g hg]
  calc
    _ = ∫⁻ x, ∫⁻ ω, g x *
        (ENNReal.ofReal (Wr (x, ω)) * K.indicator f (H (x, ω))) ∂ρ ∂σ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hright x)).symm
    _ = ∫⁻ ω, ∫⁻ x, g x *
        (ENNReal.ofReal (Wr (x, ω)) * K.indicator f (H (x, ω))) ∂σ ∂ρ :=
      lintegral_lintegral_swap hrmeas.aemeasurable
    _ = ∫⁻ ω, ∫⁻ x, f x *
        (ENNReal.ofReal (Wf (x, ω)) * K.indicator g (F (x, ω))) ∂σ ∂ρ :=
      lintegral_congr hchange
    _ = ∫⁻ x, ∫⁻ ω, f x *
        (ENNReal.ofReal (Wf (x, ω)) * K.indicator g (F (x, ω))) ∂ρ ∂σ :=
      (lintegral_lintegral_swap hfmeas.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_const_mul _ (hforward x)

include hWf hWr hF hH in
/-- The forward harmonic density gives a genuine inverse left eigenmeasure.
The only change-of-variables input is the individual noise-map identity. -/
theorem inverse_eigenmeasure (g : X → ℝ≥0∞) (hg : Measurable g) (r : ℝ≥0∞)
    (hright : ∀ᵐ x ∂σ, (∫⁻ y, g y ∂killed ρ Wf F K hK x) = r * g x)
    (hchange : ∀ (f : X → ℝ≥0∞), Measurable f → ∀ ω : Ω,
      (∫⁻ x, g x * (ENNReal.ofReal (Wr (x, ω)) * K.indicator f (H (x, ω))) ∂σ) =
        ∫⁻ x, f x * (ENNReal.ofReal (Wf (x, ω)) * K.indicator g (F (x, ω))) ∂σ) :
    killed ρ Wr H K hK ∘ₘ σ.withDensity g = r • σ.withDensity g := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun x => ∫⁻ y, f y ∂killed ρ Wr H K hK x) :=
    (Measure.measurable_lintegral hf).comp (killed ρ Wr H K hK).measurable
  rw [Measure.lintegral_bind (killed ρ Wr H K hK).aemeasurable hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul σ hg hm]
  change (∫⁻ x, g x * (∫⁻ y, f y ∂killed ρ Wr H K hK x) ∂σ) = _
  rw [bilinear_duality σ ρ Wf Wr hWf hWr F H hF hH K hK f g hf hg (hchange f hf),
    lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul σ hg hf]
  calc
    _ = ∫⁻ x, f x * (r * g x) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hright] with x hx
      rw [hx]
    _ = r * ∫⁻ x, g x * f x ∂σ := by
      calc
        _ = ∫⁻ x, r * (g x * f x) ∂σ := by
          apply lintegral_congr
          intro x
          ac_rfl
        _ = _ := lintegral_const_mul r (show Measurable (fun x => g x * f x) from hg.mul hf)

end LeanShared.AnnealedKernelDuality
