module
public import LeanShared.Analysis.BoundedInputPhysicalKernelComposition
public import LeanShared.Analysis.FourierSchwartzKernel

/-! Fixed Schwartz convolution evaluation is a bounded linear functional
on actual bounded continuous functions. This identifies completed physical
blocks by density without a supplied convolution representation. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.SchwartzConvolutionEvaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable (μ : Measure E) [μ.IsAddHaarMeasure] (k : 𝓢(E,ℂ))
    (x : E) (f : E→ᵇℂ) : Integrable (fun y => k (x-y)*f y) μ :=
  (k.integrable.comp_sub_left x).mul_bdd f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

@[expose] def linear (μ : Measure E) [μ.IsAddHaarMeasure] (k : 𝓢(E,ℂ)) (x : E) :
    (E→ᵇℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ y,k (x-y)*f y ∂μ
  map_add' f g := by
    simp only [BoundedContinuousFunction.add_apply,mul_add]
    exact integral_add (integrable μ k x f) (integrable μ k x g)
  map_smul' c f := by
    change (∫ y,k (x-y)*(c*f y) ∂μ)=c*(∫ y,k (x-y)*f y ∂μ)
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => by ring)

theorem bound (μ : Measure E) [μ.IsAddHaarMeasure] (k : 𝓢(E,ℂ)) (x : E) (f : E→ᵇℂ) :
    ‖linear μ k x f‖≤(∫ y,‖k y‖ ∂μ)*‖f‖ := by
  have major := integral_mono_ae (integrable μ k x f).norm
    (((k.integrable.comp_sub_left x).norm).mul_const ‖f‖)
    (Filter.Eventually.of_forall (fun y => by
      change ‖k (x-y)*f y‖≤‖k (x-y)‖*‖f‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)))
  rw [integral_mul_const,integral_sub_left_eq_self (fun y => ‖k y‖) μ x] at major
  exact (norm_integral_le_integral_norm _).trans major

@[expose] def evaluation (μ : Measure E) [μ.IsAddHaarMeasure] (k : 𝓢(E,ℂ)) (x : E) :
    (E→ᵇℂ) →L[ℂ] ℂ := (linear μ k x).mkContinuous (∫ y,‖k y‖ ∂μ) (bound μ k x)

theorem evaluation_apply (μ : Measure E) [μ.IsAddHaarMeasure] (k : 𝓢(E,ℂ)) (x : E) (f : E→ᵇℂ) :
    evaluation μ k x f=∫ y,k (x-y)*f y ∂μ := rfl

end LeanShared.SchwartzConvolutionEvaluation
