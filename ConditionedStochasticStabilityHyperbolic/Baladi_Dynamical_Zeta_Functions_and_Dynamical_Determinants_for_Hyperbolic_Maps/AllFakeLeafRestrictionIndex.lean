module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafOpenRestriction
public import LeanShared.Analysis.FakeLeafLinearImage

/-! Open localization preserves the literal fake-leaf family, including its
secant predicate. The restricted induced volume is the actual open restriction. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def restrictIndex (U : Submodule ℝ E) {C : Set E} (cone : ConeData U C)
    (Γ : Index U C) (O : Set E) (openO : IsOpen O) : Index U C := by
  refine ⟨Γ.val ∩ O, Γ.property.1.inter_open (slope_positive U C cone).le
    (slope_bound U C cone Γ) openO, ?_⟩
  apply FakeLeafLinearImage.leafError_zero_of_chords cone.stable_positive cone.normal_planes
  intro x hx y hy different
  exact FakeLeafGeometry.normalError_eq_zero_of_leafError_zero cone.stable_positive
    cone.normal_planes Γ.property.2 hx.1 hy.1 different

theorem restrictIndex_volume (U : Submodule ℝ E) {C : Set E} (cone : ConeData U C)
    (μ : Measure U) [μ.IsAddHaarMeasure] (Γ : Index U C)
    (O : Set E) (openO : IsOpen O) :
    EmbeddedSubmanifoldVolume.volume U μ (restrictIndex U cone Γ O openO).val =
      (EmbeddedSubmanifoldVolume.volume U μ Γ.val).restrict O :=
  (Γ.property.1.restrict_volume_open μ (slope_positive U C cone).le
    (slope_bound U C cone Γ) openO).symm

omit [BorelSpace E] in
theorem volume_empty (U : Submodule ℝ E) (μ : Measure U) :
    EmbeddedSubmanifoldVolume.volume U μ (∅ : Set E) = 0 := by
  classical
  simp [EmbeddedSubmanifoldVolume.volume, EmbeddedSubmanifoldVolume.intrinsic]

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
