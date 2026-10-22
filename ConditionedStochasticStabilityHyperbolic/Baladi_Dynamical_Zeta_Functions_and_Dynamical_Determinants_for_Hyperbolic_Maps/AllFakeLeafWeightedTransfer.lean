module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageTransport

/-! The positive weighted transfer bound on the actual entire fake-leaf
family follows from the constructed nonlinear tangent-volume formula.
No pushforward-measure estimate is supplied. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_transfer_bound (U:Submodule ℝ E) {C D:Set E}
    (sourceCone:ConeData U C) (targetCone:ConeData U D)
    (μ:Measure U) [μ.IsAddHaarMeasure] (Γ:Index U C) [Nonempty Γ.val]
    (F:OpenPartialHomeomorph E E) (inside:Γ.val⊆F.source)
    (forward:ContDiffOn ℝ 1 F F.source) (backward:ContDiffOn ℝ 1 F.symm F.target)
    (measurableF:Measurable F) (image:Index U D) (imageEq:image.val=F '' Γ.val)
    (a f:E→ℝ≥0∞) (ma:Measurable a) (mf:Measurable f) (cost:ℝ≥0) (B:ℝ≥0∞)
    (leafBound:∀Δ:Index U D,∫⁻y,f y ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val≤B)
    (jacobian : let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ.val
        (slope_positive U C sourceCone).le (slope_bound U C sourceCone Γ));
      ∀ u ∈ FakeLeafGraph.parameterDomain U Γ.val, a (gS u) ≤ (cost : ℝ≥0∞) *
        ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
          (fderiv ℝ gS u).toLinearMap.range).normDet)) :
    (∫⁻x,a x*f (F x) ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val)≤(cost:ℝ≥0∞)*B:=by
  have targetSlope:∀x∈F '' Γ.val,∀y∈F '' Γ.val,
      ‖Uᗮ.starProjection (x-y)‖≤slope U D targetCone*‖U.starProjection (x-y)‖:=by
    rw [←imageEq]
    exact slope_bound U D targetCone image
  have dominated:=Γ.property.1.image_weighted_volume_le μ
    (slope_positive U C sourceCone).le (slope_positive U D targetCone).le
    (slope_bound U C sourceCone Γ) F inside forward backward targetSlope measurableF a ma cost jacobian
  rw [←imageEq] at dominated
  let ν:=EmbeddedSubmanifoldVolume.volume U μ Γ.val
  calc
    _=∫⁻x,f (F x) ∂ν.withDensity a:=
      (lintegral_withDensity_eq_lintegral_mul ν ma (mf.comp measurableF)).symm
    _=∫⁻y,f y ∂(ν.withDensity a).map F:=(lintegral_map mf measurableF).symm
    _≤∫⁻y,f y ∂((cost:ℝ≥0∞) • EmbeddedSubmanifoldVolume.volume U μ image.val):=
      lintegral_mono' dominated le_rfl
    _=(cost:ℝ≥0∞)*(∫⁻y,f y ∂EmbeddedSubmanifoldVolume.volume U μ image.val):=by
      rw [lintegral_smul_measure]
      rfl
    _≤(cost:ℝ≥0∞)*B:=mul_le_mul_of_nonneg_left (leafBound image) bot_le
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
