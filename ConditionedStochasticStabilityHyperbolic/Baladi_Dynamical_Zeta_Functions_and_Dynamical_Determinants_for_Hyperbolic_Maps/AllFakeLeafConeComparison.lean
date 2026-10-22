module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTwoKernelBound
public import LeanShared.Analysis.FakeLeafConeMonotonicity
public import LeanShared.Analysis.ConeFourierBlocks

/-! Literal cone enlargement includes every source fake leaf, with its same
induced volume. Actual Fourier convolution therefore has the required
between-cone leaf integral bound; no norm-comparison source is used. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def includeLeaf (U : Submodule ℝ E) {C D : Set E}
    (cone : ConeData U C) (inside : C⊆D) (Γ : Index U C) : Index U D :=
  ⟨Γ.val,Γ.property.1,FakeLeafGeometry.leafError_zero_mono inside
    cone.stable_positive cone.normal_planes Γ.property.2⟩

theorem convolution_cone_bound (U : Submodule ℝ E) {C D : Set E}
    (cone : ConeData U C) (inside : C⊆D)
    (μ : Measure U) [μ.IsAddHaarMeasure]
    (σ f : 𝓢(E,ℂ)) (B : ℝ≥0∞)
    (bound : ∀ Δ : Index U D,∫⁻ x,‖f x‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val≤B) (Γ : Index U C) :
    (∫⁻ x,‖ConeFourierBlocks.block σ f x‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val)≤
      (∫⁻ z,‖FourierSchwartzKernel.kernel σ z‖ₑ)*B := by
  calc
    _ ≤ ∫⁻ x,∫⁻ y,‖FourierSchwartzKernel.kernel σ (x-y)‖ₑ*‖f y‖ₑ
        ∂volume ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ConeFourierBlocks.block_apply]
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
        (fun y=>FourierSchwartzKernel.kernel σ (x-y)*f y)
    _ ≤ _ := physical_positive_convolution_bound U cone μ volume
      (fun z=>‖FourierSchwartzKernel.kernel σ z‖ₑ) (fun x=>‖f x‖ₑ)
      (FourierSchwartzKernel.kernel σ).continuous.measurable.enorm f.continuous.measurable.enorm B
      (fun Δ=>bound (includeLeaf U cone inside Δ)) Γ
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
