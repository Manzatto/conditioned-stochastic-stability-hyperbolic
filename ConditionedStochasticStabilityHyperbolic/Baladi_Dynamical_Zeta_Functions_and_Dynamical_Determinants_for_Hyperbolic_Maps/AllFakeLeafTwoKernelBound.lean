module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafLocalizedTransfer
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafPositiveConvolution
public import LeanShared.Analysis.PositiveConvolutionSubstitution

/-! Actual ambient convolution, local nonlinear transport and a second
ambient convolution are bounded on the full induced fake-leaf L1 family. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem physical_positive_convolution_bound (U : Submodule ℝ E) {C : Set E}
    (cone : ConeData U C) (μ : Measure U) [μ.IsAddHaarMeasure]
    (ambient : Measure E) [ambient.IsAddHaarMeasure]
    (k f : E → ℝ≥0∞) (mk : Measurable k) (mf : Measurable f) (B : ℝ≥0∞)
    (bound : ∀ Γ : Index U C,
      ∫⁻ x, f x ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val ≤ B)
    (Γ : Index U C) :
    (∫⁻ x, ∫⁻ y, k (x-y)*f y ∂ambient
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤ (∫⁻ z, k z ∂ambient)*B := by
  simp_rw [PositiveConvolutionSubstitution.identity ambient k f mk mf]
  by_cases nonempty : Nonempty Γ.val
  · let : Nonempty Γ.val := nonempty
    exact positive_convolution_bound U cone μ ambient k f mk mf B bound Γ
  · have empty : Γ.val = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact nonempty ⟨⟨x,hx⟩⟩
    rw [empty, volume_empty, lintegral_zero_measure]
    exact bot_le

theorem two_kernel_bound (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D)
    (μ : Measure U) [μ.IsAddHaarMeasure]
    (ambient : Measure E) [ambient.IsAddHaarMeasure]
    (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (measurableF : Measurable F) (O : Set E) (openO : IsOpen O) (inside : O ⊆ F.source)
    (images : ∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val)
    {K : ℝ} (nonnegative : 0 ≤ K)
    (inverse : ∀ x ∈ O, ‖fderiv ℝ F.symm (F x)‖ ≤ K)
    (k₀ k₁ u : E → ℝ≥0∞) (m₀ : Measurable k₀) (m₁ : Measurable k₁)
    (mu : Measurable u) (B : ℝ≥0∞)
    (leafBound : ∀ Δ : Index U D,
      ∫⁻ y, u y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B)
    (Γ : Index U C) :
    (∫⁻ x, ∫⁻ w, k₀ (x-w)*O.indicator
      (fun z => ∫⁻ y, k₁ (F z-y)*u y ∂ambient) w ∂ambient
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
      (∫⁻ z, k₀ z ∂ambient)*
        (ENNReal.ofReal (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K)*
          ((∫⁻ z, k₁ z ∂ambient)*B)) := by
  let inner : E → ℝ≥0∞ := fun z => ∫⁻ y, k₁ (z-y)*u y ∂ambient
  have measurableInner : Measurable inner :=
    ((m₁.comp (measurable_fst.sub measurable_snd)).mul (mu.comp measurable_snd)).lintegral_prod_right'
  have innerBound (Δ : Index U D) :
      ∫⁻ y, inner y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤
        (∫⁻ z, k₁ z ∂ambient)*B :=
    physical_positive_convolution_bound U targetCone μ ambient k₁ u m₁ mu B leafBound Δ
  have localizedBound (Δ : Index U C) := localized_transfer_bound U sourceCone targetCone μ F
    forward backward measurableF O openO inside images nonnegative inverse inner measurableInner
    ((∫⁻ z, k₁ z ∂ambient)*B) innerBound Δ
  exact physical_positive_convolution_bound U sourceCone μ ambient k₀
    (O.indicator (fun z => inner (F z))) m₀
    ((measurableInner.comp measurableF).indicator openO.measurableSet)
    _ localizedBound Γ

theorem exists_two_kernel_radius (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D) (A : E ≃L[ℝ] E)
    (strict : ∀ v ∈ C ∩ Metric.sphere (0 : E) 1,
      FakeLeafLinearImage.adjointEquiv A.symm v ∈ interior D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure U) [μ.IsAddHaarMeasure]
      (ambient : Measure E) [ambient.IsAddHaarMeasure]
      (F : OpenPartialHomeomorph E E) (O : Set E),
      IsOpen O → Convex ℝ O → O ⊆ F.source →
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target → Measurable F →
      (∀ x ∈ O, ‖fderiv ℝ F x - A.toContinuousLinearMap‖ ≤ δ) →
      ∀ K : ℝ, 0 ≤ K → (∀ x ∈ O, ‖fderiv ℝ F.symm (F x)‖ ≤ K) →
      ∀ k₀ k₁ u : E → ℝ≥0∞, Measurable k₀ → Measurable k₁ → Measurable u →
      ∀ B : ℝ≥0∞,
      (∀ Δ : Index U D, ∫⁻ y, u y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B) →
      ∀ Γ : Index U C,
      (∫⁻ x, ∫⁻ w, k₀ (x-w)*O.indicator
        (fun z => ∫⁻ y, k₁ (F z-y)*u y ∂ambient) w ∂ambient
        ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
        (∫⁻ z, k₀ z ∂ambient)*
          (ENNReal.ofReal (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K)*
            ((∫⁻ z, k₁ z ∂ambient)*B)) := by
  obtain ⟨δ, positive, image⟩ := exists_nonlinear_image_radius U sourceCone targetCone A strict
  refine ⟨δ, positive, ?_⟩
  intro μ _ ambient _ F O openO convex inside forward backward measurableF comparison
    K nonnegative inverse k₀ k₁ u m₀ m₁ mu B leafBound Γ
  exact two_kernel_bound U sourceCone targetCone μ ambient F forward backward measurableF
    O openO inside (image F O convex inside forward backward comparison)
    nonnegative inverse k₀ k₁ u m₀ m₁ mu B leafBound Γ

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
