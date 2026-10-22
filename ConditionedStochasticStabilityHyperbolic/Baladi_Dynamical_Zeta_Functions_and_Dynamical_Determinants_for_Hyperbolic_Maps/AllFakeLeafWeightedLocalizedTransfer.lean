module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafWeightedTransfer
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafRestrictionIndex
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTwoKernelBound

/-! The principal localized transfer retains the joint pointwise weight /
actual leaf Jacobian bound. No separate suprema of these factors are taken. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_localized_transfer_bound (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D)
    (μ : Measure U) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (measurableF : Measurable F) (O : Set E) (openO : IsOpen O) (inside : O ⊆ F.source)
    (images : ∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val)
    (a f : E → ℝ≥0∞) (ma : Measurable a) (mf : Measurable f)
    (supported : ∀ x ∉ O, a x = 0) (cost : ℝ≥0) (B : ℝ≥0∞)
    (leafBound : ∀ Δ : Index U D,
      ∫⁻ y, f y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B)
    (jacobian : ∀ Γ : Index U C, Γ.val ⊆ O →
      let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ.val
        (slope_positive U C sourceCone).le (slope_bound U C sourceCone Γ));
      ∀ u ∈ FakeLeafGraph.parameterDomain U Γ.val, a (gS u) ≤ (cost : ℝ≥0∞)*
        ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
          (fderiv ℝ gS u).toLinearMap.range).normDet))
    (Γ : Index U C) :
    (∫⁻ x,a x*f (F x) ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤ (cost : ℝ≥0∞)*B := by
  let small := restrictIndex U sourceCone Γ O openO
  have localization :
      (∫⁻ x,a x*f (F x) ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) =
      ∫⁻ x,a x*f (F x) ∂EmbeddedSubmanifoldVolume.volume U μ small.val := by
    rw [restrictIndex_volume U sourceCone μ Γ O openO, ←lintegral_indicator openO.measurableSet]
    apply lintegral_congr
    intro x
    by_cases member : x ∈ O
    · rw [indicator_of_mem member]
    · rw [indicator_of_notMem member, supported x member, zero_mul]
  rw [localization]
  by_cases nonempty : Nonempty small.val
  · let : Nonempty small.val := nonempty
    have smallInside : small.val ⊆ O := inter_subset_right
    obtain ⟨image,imageEq⟩ := images small smallInside
    exact weighted_transfer_bound U sourceCone targetCone μ small F (smallInside.trans inside)
      forward backward measurableF image imageEq a f ma mf cost B leafBound
      (jacobian small smallInside)
  · have empty : small.val = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact nonempty ⟨⟨x,hx⟩⟩
    rw [empty,volume_empty,lintegral_zero_measure]
    exact bot_le

theorem weighted_convolution_transfer_bound (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D)
    (μ : Measure U) [μ.IsAddHaarMeasure] (ambient : Measure E) [ambient.IsAddHaarMeasure]
    (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (measurableF : Measurable F) (O : Set E) (openO : IsOpen O) (inside : O ⊆ F.source)
    (images : ∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val)
    (k a f : E → ℝ≥0∞) (mk : Measurable k) (ma : Measurable a) (mf : Measurable f)
    (supported : ∀ x ∉ O, a x = 0) (cost : ℝ≥0) (B : ℝ≥0∞)
    (leafBound : ∀ Δ : Index U D,
      ∫⁻ y, f y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B)
    (jacobian : ∀ Γ : Index U C, Γ.val ⊆ O →
      let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ.val
        (slope_positive U C sourceCone).le (slope_bound U C sourceCone Γ));
      ∀ u ∈ FakeLeafGraph.parameterDomain U Γ.val, a (gS u) ≤ (cost : ℝ≥0∞)*
        ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
          (fderiv ℝ gS u).toLinearMap.range).normDet))
    (Γ : Index U C) :
    (∫⁻ x,∫⁻ w,k (x-w)*(a w*f (F w)) ∂ambient
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
      (∫⁻ z,k z ∂ambient)*((cost : ℝ≥0∞)*B) :=
  physical_positive_convolution_bound U sourceCone μ ambient k (fun w => a w*f (F w))
    mk (ma.mul (mf.comp measurableF)) _
    (weighted_localized_transfer_bound U sourceCone targetCone μ F forward backward measurableF
      O openO inside images a f ma mf supported cost B leafBound jacobian) Γ

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
