module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafWeightedTransfer
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafRestrictionIndex
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNonlinearImage
public import LeanShared.Analysis.LocalDiffeomorphismCoarseJacobian

/-! The actual localized nonlinear transfer is bounded on the full induced
leaf-volume supremum. Its weak constant comes from the genuine inverse
derivative, rather than a supplied tangent-volume inequality. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem localized_transfer_bound (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D)
    (μ : Measure U) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (measurableF : Measurable F) (O : Set E) (openO : IsOpen O) (inside : O ⊆ F.source)
    (images : ∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val)
    {K : ℝ} (nonnegative : 0 ≤ K)
    (inverse : ∀ x ∈ O, ‖fderiv ℝ F.symm (F x)‖ ≤ K)
    (f : E → ℝ≥0∞) (mf : Measurable f) (B : ℝ≥0∞)
    (leafBound : ∀ Δ : Index U D,
      ∫⁻ y, f y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B)
    (Γ : Index U C) :
    (∫⁻ x, O.indicator (fun y => f (F y)) x
      ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
      ENNReal.ofReal (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K) * B := by
  let small := restrictIndex U sourceCone Γ O openO
  rw [lintegral_indicator openO.measurableSet,
    ← restrictIndex_volume U sourceCone μ Γ O openO]
  change (∫⁻ x, f (F x) ∂EmbeddedSubmanifoldVolume.volume U μ small.val) ≤ _
  by_cases nonempty : Nonempty small.val
  · let : Nonempty small.val := nonempty
    have smallInside : small.val ⊆ O := inter_subset_right
    obtain ⟨image, imageEq⟩ := images small smallInside
    let cost : ℝ≥0 := ⟨GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K,
      GraphJacobian.densityBound_nonneg K⟩
    have costEq : (cost : ℝ≥0∞) =
        ENNReal.ofReal (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    have estimate := weighted_transfer_bound U sourceCone targetCone μ small F
      (smallInside.trans inside) forward backward measurableF image imageEq (fun _ => 1) f
      measurable_const mf cost B leafBound ?_
    · simpa only [one_mul, costEq] using estimate
    · dsimp only
      intro u hu
      let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U small.val
        (slope_positive U C sourceCone).le (slope_bound U C sourceCone small))
      have member : gS u ∈ small.val :=
        (FakeLeafGraph.graphExtension_image U small.val (slope_positive U C sourceCone).le
          (slope_bound U C sourceCone small)).subset ⟨u, hu, rfl⟩
      have geometric := LocalDiffeomorphismCoarseJacobian.uniform_bound F forward backward
        (inside (smallInside member)) (fderiv ℝ gS u).toLinearMap.range nonnegative
        (inverse (gS u) (smallInside member))
      have positiveBound := ENNReal.ofReal_le_ofReal geometric
      rw [ENNReal.ofReal_one, ENNReal.ofReal_mul (GraphJacobian.densityBound_nonneg K)] at positiveBound
      rw [ENNReal.coe_nnreal_eq]
      exact positiveBound
  · have empty : small.val = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact nonempty ⟨⟨x, hx⟩⟩
    rw [empty, volume_empty, lintegral_zero_measure]
    exact bot_le

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
