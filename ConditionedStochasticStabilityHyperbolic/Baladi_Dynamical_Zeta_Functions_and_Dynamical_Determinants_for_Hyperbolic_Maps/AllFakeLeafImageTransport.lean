module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageCoordinates
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafParametricVolume
public import LeanShared.MeasureTheory.WeightedPushforward

/-! Exact nonlinear transport of actual induced leaf volume. The tangent
Jacobian is the genuine restricted ambient differential, and the coordinate
change is constructed from the source/image leaves. -/
public noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem C1Embedded.image_tangent_volume {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (source : C1Embedded U Γ) (μ : Measure U) [μ.IsAddHaarMeasure]
    {LS LT : ℝ} (hLS : 0 ≤ LS) (hLT : 0 ≤ LT)
    (sourceSlope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LS * ‖U.starProjection (x-y)‖)
    (F : OpenPartialHomeomorph E E) (inside : Γ ⊆ F.source)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (targetSlope : ∀ x ∈ F '' Γ, ∀ y ∈ F '' Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LT * ‖U.starProjection (x-y)‖) :
    let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hLS sourceSlope)
    ((μ.restrict (FakeLeafGraph.parameterDomain U Γ)).withDensity (fun u =>
      ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
        (fderiv ℝ gS u).toLinearMap.range).normDet) *
      IntrinsicCoordinatePatchMeasures.density gS (FakeLeafGraph.parameterDomain U Γ) u)).map
        (F ∘ gS) = EmbeddedSubmanifoldVolume.volume U μ (F '' Γ) := by
  intro gS
  let image := F.homeomorphOfImageSubsetSource inside rfl
  let : Nonempty (F '' Γ) := ⟨image (Classical.choice ‹Nonempty Γ›)⟩
  have target := source.image_local_diffeomorphism hLS sourceSlope F inside forward backward
  let gT := ConeGraphGeometry.graphPoint U
    (FakeLeafGraph.heightExtension U (F '' Γ) hLT targetSlope)
  obtain ⟨h, sourceDomain, targetDomain, coordinateRegular, agrees⟩ :=
    source.exists_image_coordinates hLS hLT sourceSlope F inside forward backward targetSlope
  have sourceRegular : ContDiffOn ℝ 1 gS h.source := by
    rw [sourceDomain]
    exact U.subtypeL.contDiff.contDiffOn.add
      (Uᗮ.subtypeL.contDiff.comp_contDiffOn (source.heightExtension_contDiffOn hLS sourceSlope))
  have targetRegular : ContDiffOn ℝ 1 gT h.target := by
    rw [targetDomain]
    exact U.subtypeL.contDiff.contDiffOn.add
      (Uᗮ.subtypeL.contDiff.comp_contDiffOn (target.heightExtension_contDiffOn hLT targetSlope))
  have imageSource : MapsTo gS h.source F.source := by
    intro u hu
    apply inside
    exact (FakeLeafGraph.graphExtension_image U Γ hLS sourceSlope).subset
      ⟨u, sourceDomain ▸ hu, rfl⟩
  have result := ParametrizedImmersionTransport.map_tangent_density μ h gS gT F
    sourceRegular targetRegular coordinateRegular
    (fun u hu => ((forward.differentiableOn one_ne_zero) (gS u)
      (imageSource hu)).differentiableAt (F.open_source.mem_nhds (imageSource hu))) agrees
  rw [sourceDomain, targetDomain] at result
  exact result.trans (target.graph_parametric_volume μ hLT targetSlope).symm
/-- Pointwise control by the genuine tangent Jacobian gives domination of
actual induced leaf measures. The Jacobian transport law is constructed above. -/
theorem C1Embedded.image_weighted_volume_le {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (source : C1Embedded U Γ) (μ : Measure U) [μ.IsAddHaarMeasure]
    {LS LT : ℝ} (hLS : 0 ≤ LS) (hLT : 0 ≤ LT)
    (sourceSlope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LS * ‖U.starProjection (x-y)‖)
    (F : OpenPartialHomeomorph E E) (inside : Γ ⊆ F.source)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (targetSlope : ∀ x ∈ F '' Γ, ∀ y ∈ F '' Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LT * ‖U.starProjection (x-y)‖)
    (measurableF : Measurable F) (a : E → ℝ≥0∞) (measurableA : Measurable a) (C : ℝ≥0)
    (cost : let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hLS sourceSlope);
      ∀ u ∈ FakeLeafGraph.parameterDomain U Γ, a (gS u) ≤ (C : ℝ≥0∞) *
        ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
          (fderiv ℝ gS u).toLinearMap.range).normDet)) :
    ((EmbeddedSubmanifoldVolume.volume U μ Γ).withDensity a).map F ≤
      (C : ℝ≥0∞) • EmbeddedSubmanifoldVolume.volume U μ (F '' Γ) := by
  let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hLS sourceSlope)
  let S := FakeLeafGraph.parameterDomain U Γ
  let jS := IntrinsicCoordinatePatchMeasures.density gS S
  let jT : U → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
      (fderiv ℝ gS u).toLinearMap.range).normDet) * jS u
  have gMeasurable : Measurable gS :=
    continuous_subtype_val.measurable.add
      (continuous_subtype_val.measurable.comp
        (FakeLeafGraph.heightExtension_measurable U Γ hLS sourceSlope source.measurableSet))
  have graphRegular : ContDiffOn ℝ 1 gS S :=
    U.subtypeL.contDiff.contDiffOn.add
      (Uᗮ.subtypeL.contDiff.comp_contDiffOn (source.heightExtension_contDiffOn hLS sourceSlope))
  have jMeasurable : Measurable jS :=
    IntrinsicCoordinatePatchMeasures.measurable_density graphRegular (source.projection_open hLS sourceSlope)
  have sourceMeasure : EmbeddedSubmanifoldVolume.volume U μ Γ =
      ((μ.restrict S).withDensity jS).map gS := source.graph_parametric_volume μ hLS sourceSlope
  have targetMeasure : ((μ.restrict S).withDensity jT).map (F ∘ gS) =
      EmbeddedSubmanifoldVolume.volume U μ (F '' Γ) :=
    source.image_tangent_volume μ hLS hLT sourceSlope F inside forward backward targetSlope
  have weighted : ((EmbeddedSubmanifoldVolume.volume U μ Γ).withDensity a).map F =
      ((μ.restrict S).withDensity (fun u => jS u * a (gS u))).map (F ∘ gS) := by
    rw [sourceMeasure, ← WeightedPushforward.map_withDensity_comp _ gMeasurable.aemeasurable measurableA,
      Measure.map_map measurableF gMeasurable,
      ← withDensity_mul _ jMeasurable (measurableA.comp gMeasurable)]
    rfl
  have dominated : (μ.restrict S).withDensity (fun u => jS u * a (gS u)) ≤
      (μ.restrict S).withDensity (fun u => (C : ℝ≥0∞) * jT u) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (source.projection_open hLS sourceSlope).measurableSet] with u hu
    calc
      _ ≤ jS u * ((C : ℝ≥0∞) * ENNReal.ofReal
          (((fderiv ℝ F (gS u)).toLinearMap.domRestrict
            (fderiv ℝ gS u).toLinearMap.range).normDet)) :=
        mul_le_mul_of_nonneg_left (cost u hu) bot_le
      _ = _ := by dsimp only [jT]; ring
  have scalar : (μ.restrict S).withDensity (fun u => (C : ℝ≥0∞) * jT u) =
      (C : ℝ≥0∞) • (μ.restrict S).withDensity jT := by
    exact withDensity_smul' (C : ℝ≥0∞) jT ENNReal.coe_ne_top
  have mapped := Measure.map_mono dominated (measurableF.comp gMeasurable)
  rw [scalar, Measure.map_smul _ (measurableF.comp gMeasurable).aemeasurable, targetMeasure] at mapped
  exact weighted.trans_le mapped
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
