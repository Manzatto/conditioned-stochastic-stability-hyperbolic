module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTwoKernelBound
public import LeanShared.Analysis.PositiveKernelComposition

/-! A physical complex kernel dominated by the proved spatial majorant
gives an actual operator row bound in induced leaf volume. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem physical_kernel_row_bound (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D)
    (μ : Measure U) [μ.IsAddHaarMeasure]
    (ambient : Measure E) [ambient.IsAddHaarMeasure]
    (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (measurableF : Measurable F) (O : Set E) (openO : IsOpen O) (inside : O ⊆ F.source)
    (images : ∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val)
    {K : ℝ} (nonnegative : 0 ≤ K)
    (inverse : ∀ x ∈ O, ‖fderiv ℝ F.symm (F x)‖ ≤ K)
    (k₀ k₁ : E → ℝ≥0∞) (m₀ : Measurable k₀) (m₁ : Measurable k₁)
    (u : E → ℂ) (mu : Measurable u) (kernel : E → E → ℂ) (constant : ℝ≥0)
    (majorant : ∀ x y, ‖kernel x y‖ₑ ≤ (constant : ℝ≥0∞)*
      (∫⁻ w, k₀ (x-w)*(O.indicator (fun _ => 1) w)*k₁ (F w-y) ∂ambient))
    (B : ℝ≥0∞)
    (leafBound : ∀ Δ : Index U D,
      ∫⁻ y, ‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B)
    (Γ : Index U C) :
    (∫⁻ x, ‖∫ y, kernel x y*u y ∂ambient‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
      (constant : ℝ≥0∞)*((∫⁻ z, k₀ z ∂ambient)*
        (ENNReal.ofReal (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K)*
          ((∫⁻ z, k₁ z ∂ambient)*B))) := by
  have pointwise (x : E) := PositiveKernelComposition.operator_bound ambient ambient F measurableF
    (O.indicator (fun _ => 1)) k₀ k₁ (measurable_const.indicator openO.measurableSet)
    m₀ m₁ u mu (kernel x) constant x (majorant x)
  have rewriteMajorant (x : E) :
      (∫⁻ w, k₀ (x-w)*O.indicator (fun _ => 1) w*
        (∫⁻ y, k₁ (F w-y)*‖u y‖ₑ ∂ambient) ∂ambient) =
      ∫⁻ w, k₀ (x-w)*O.indicator
        (fun z => ∫⁻ y, k₁ (F z-y)*‖u y‖ₑ ∂ambient) w ∂ambient := by
    apply lintegral_congr
    intro w
    by_cases member : w ∈ O
    · simp only [indicator_of_mem member, mul_one]
    · simp only [indicator_of_notMem member, mul_zero, zero_mul]
  simp_rw [rewriteMajorant] at pointwise
  calc
    _ ≤ ∫⁻ x, (constant : ℝ≥0∞)*(∫⁻ w, k₀ (x-w)*O.indicator
        (fun z => ∫⁻ y, k₁ (F z-y)*‖u y‖ₑ ∂ambient) w ∂ambient)
        ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val := lintegral_mono pointwise
    _ = (constant : ℝ≥0∞)*(∫⁻ x, ∫⁻ w, k₀ (x-w)*O.indicator
        (fun z => ∫⁻ y, k₁ (F z-y)*‖u y‖ₑ ∂ambient) w ∂ambient
        ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (two_kernel_bound U sourceCone targetCone μ ambient F forward backward measurableF O openO
        inside images nonnegative inverse k₀ k₁ (fun y => ‖u y‖ₑ) m₀ m₁ mu.enorm B leafBound Γ) bot_le

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
