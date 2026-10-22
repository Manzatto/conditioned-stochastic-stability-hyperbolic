module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTranslation
public import Mathlib.MeasureTheory.Measure.Prod

/-! Positive convolution is bounded on the actual full fake-leaf L¹
supremum. Translation of induced leaf volume is proved, not assumed. -/
public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem positive_convolution_bound (U : Submodule ℝ E) {C : Set E}
    (cone : ConeData U C) (μ : Measure U) [μ.IsAddHaarMeasure]
    (ambient : Measure E) [SFinite ambient]
    (k f : E → ℝ≥0∞) (mk : Measurable k) (mf : Measurable f) (B : ℝ≥0∞)
    (bound : ∀ Γ : Index U C,
      ∫⁻ x, f x ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val ≤ B)
    (Γ : Index U C) [Nonempty Γ.val] :
    (∫⁻ x, ∫⁻ z, k z * f (x - z) ∂ambient
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤ (∫⁻ z, k z ∂ambient) * B := by
  let ν := EmbeddedSubmanifoldVolume.volume U μ Γ.val
  let : SFinite ν := by
    dsimp only [ν]
    rw [Γ.property.1.graph_parametric_volume μ (slope_positive U C cone).le (slope_bound U C cone Γ)]
    infer_instance
  have translatedBound (z : E) : (∫⁻ x, f (x - z) ∂ν) ≤ B := by
    obtain ⟨image, _, volume⟩ := exists_translated_leaf U cone μ Γ (-z)
    have actual := lintegral_map (μ := ν) (f := f) (g := fun x : E => x + -z) mf
      (continuous_id.add continuous_const).measurable
    rw [volume] at actual
    simpa only [sub_eq_add_neg] using actual.symm.trans_le (bound image)
  have joint : Measurable (fun p : E × E => k p.2 * f (p.1 - p.2)) :=
    (mk.comp measurable_snd).mul (mf.comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap joint.aemeasurable]
  calc
    _ ≤ ∫⁻ z, k z * B ∂ambient := by
      apply lintegral_mono
      intro z
      change (∫⁻ x, k z * f (x - z) ∂ν) ≤ k z * B
      rw [lintegral_const_mul (μ := ν) (k z) (f := fun x : E => f (x - z))
        (mf.comp (measurable_id.sub measurable_const))]
      exact mul_le_mul_of_nonneg_left (translatedBound z) bot_le
    _ = _ := lintegral_mul_const B mk
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
