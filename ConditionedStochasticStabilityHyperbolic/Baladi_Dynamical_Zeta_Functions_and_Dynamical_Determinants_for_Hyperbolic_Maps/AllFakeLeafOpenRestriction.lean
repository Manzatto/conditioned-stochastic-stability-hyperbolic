module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageImmersion
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCharts
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafParametricVolume
public import Mathlib.Topology.Constructions
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph

/-! Localizing an actual fake leaf to an open chart window constructs its
embedded C¹ structure rather than introducing a localized-leaf source. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem graph_projection_value (U : Submodule ℝ E) (Γ : Set E)
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) (x : Γ) :
    ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope)
      (FakeLeafGraph.projection U Γ x) = x.val := by
  change (FakeLeafGraph.projection U Γ x : E) +
    (FakeLeafGraph.heightExtension U Γ hL slope (FakeLeafGraph.projection U Γ x) : E) = x.val
  rw [FakeLeafGraph.heightExtension_on_domain U Γ hL slope ⟨_, x, rfl⟩]
  rw [← FakeLeafGraph.point_eq_graph U Γ hL slope ⟨_, x, rfl⟩,
    FakeLeafGraph.point_of_projection]

theorem C1Embedded.inter_open {U : Submodule ℝ E} {Γ O : Set E}
    (source : C1Embedded U Γ) {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (openO : IsOpen O) : C1Embedded U (Γ ∩ O) := by
  classical
  by_cases nonempty : Nonempty ↥(Γ ∩ O)
  · let : Nonempty ↥(Γ ∩ O) := nonempty
    let : Nonempty Γ := ⟨⟨(Classical.choice nonempty).val, (Classical.choice nonempty).property.1⟩⟩
    let i : ↥(Γ ∩ O) → Γ := Set.inclusion inter_subset_left
    let q := FakeLeafGraph.projection U Γ
    let p := q ∘ i
    let graph := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope)
    let chart := FakeLeafProjectionChart.chart U Γ hL slope (source.projection_open hL slope)
    have relative : IsOpen ((Subtype.val : Γ → E) ⁻¹' (Γ ∩ O)) := by
      have eq : (Subtype.val : Γ → E) ⁻¹' (Γ ∩ O) = Subtype.val ⁻¹' O := by
        ext x
        simp only [mem_preimage, mem_inter_iff, x.property, true_and]
      rw [eq]
      exact openO.preimage continuous_subtype_val
    have iopen : Topology.IsOpenEmbedding i := Topology.IsOpenEmbedding.inclusion inter_subset_left relative
    have popen : Topology.IsOpenEmbedding p := (chart.isOpenEmbedding rfl).comp iopen
    have inside : range p ⊆ FakeLeafGraph.parameterDomain U Γ := by
      rintro _ ⟨x, rfl⟩
      exact ⟨i x, rfl⟩
    refine ParametrizedImmersionChart.exists_chart (Γ ∩ O) p popen graph ?_ ?_
      U.orthogonalProjectionOnto ?_ ?_
    · exact (U.subtypeL.contDiff.contDiffOn.add
        (Uᗮ.subtypeL.contDiff.comp_contDiffOn (source.heightExtension_contDiffOn hL slope))).mono inside
    · intro x
      exact graph_projection_value U Γ hL slope (i x)
    · intro x
      rfl
    · intro x _
      exact U.orthogonalProjectionOnto.contDiff.contDiffAt
  · have empty : Γ ∩ O = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact nonempty ⟨⟨x, hx⟩⟩
    simpa only [empty] using embedded_empty U
variable [MeasurableSpace E] [BorelSpace E]

/-- Restricting the independently constructed induced volume to an open
window equals the induced volume on the genuinely restricted leaf. -/
theorem C1Embedded.restrict_volume_open {U : Submodule ℝ E} {Γ O : Set E}
    (source : C1Embedded U Γ) (μ : Measure U) [μ.IsAddHaarMeasure]
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (openO : IsOpen O) :
    (EmbeddedSubmanifoldVolume.volume U μ Γ).restrict O =
      EmbeddedSubmanifoldVolume.volume U μ (Γ ∩ O) := by
  have smallSlope : ∀ x ∈ Γ ∩ O, ∀ y ∈ Γ ∩ O,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖ :=
    fun x hx y hy => slope x hx.1 y hy.1
  have smallEmbedded := source.inter_open hL slope openO
  let full := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope)
  let small := ConeGraphGeometry.graphPoint U
    (FakeLeafGraph.heightExtension U (Γ ∩ O) hL smallSlope)
  let S := FakeLeafGraph.parameterDomain U Γ
  let V := FakeLeafGraph.parameterDomain U (Γ ∩ O)
  let jF := IntrinsicCoordinatePatchMeasures.density full S
  let jV := IntrinsicCoordinatePatchMeasures.density small V
  have projection (u : U) : U.orthogonalProjectionOnto (full u) = u := by
    change U.orthogonalProjectionOnto ((u : E) +
      (FakeLeafGraph.heightExtension U Γ hL slope u : E)) = u
    rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    have zero : U.orthogonalProjectionOnto
        (FakeLeafGraph.heightExtension U Γ hL slope u : E) = 0 :=
      (U.orthogonalProjectionOnto_eq_zero_iff).mpr
        (FakeLeafGraph.heightExtension U Γ hL slope u).property
    rw [zero, add_zero]
  have domain : V = S ∩ full ⁻¹' O := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨Set.inclusion inter_subset_left x, rfl⟩, ?_⟩
      change full (FakeLeafGraph.projection U Γ (Set.inclusion inter_subset_left x)) ∈ O
      have eq : full (FakeLeafGraph.projection U Γ (Set.inclusion inter_subset_left x)) = x.val :=
        graph_projection_value U Γ hL slope (Set.inclusion inter_subset_left x)
      rw [eq]
      exact x.property.2
    · rintro ⟨hu, ho⟩
      have member : full u ∈ Γ := (FakeLeafGraph.graphExtension_image U Γ hL slope).subset
        ⟨u, hu, rfl⟩
      exact ⟨⟨full u, member, ho⟩, projection u⟩
  have same (u : U) (hu : u ∈ V) : small u = full u := by
    obtain ⟨x, hx⟩ := hu
    subst u
    exact (graph_projection_value U (Γ ∩ O) hL smallSlope x).trans
      (graph_projection_value U Γ hL slope (Set.inclusion inter_subset_left x)).symm
  have Vopen : IsOpen V := smallEmbedded.projection_open hL smallSlope
  have density (u : U) (hu : u ∈ V) : jV u = jF u := by
    have nearby : small =ᶠ[𝓝 u] full := by
      filter_upwards [Vopen.mem_nhds hu] with v hv
      exact same v hv
    have sourceMem : u ∈ S := (domain ▸ hu).1
    dsimp only [jV, jF]
    simp only [IntrinsicCoordinatePatchMeasures.density, indicator_of_mem hu,
      indicator_of_mem sourceMem]
    rw [nearby.fderiv_eq]
  have fullMeasurable : Measurable full :=
    continuous_subtype_val.measurable.add (continuous_subtype_val.measurable.comp
      (FakeLeafGraph.heightExtension_measurable U Γ hL slope source.measurableSet))
  let ρ := (μ.restrict V).withDensity jV
  have weights : ρ = (μ.restrict V).withDensity jF := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem Vopen.measurableSet] with u hu
    exact density u hu
  have maps : ρ.map small = ρ.map full := by
    apply Measure.map_congr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem Vopen.measurableSet] with u hu
    exact same u hu
  have restricted : (EmbeddedSubmanifoldVolume.volume U μ Γ).restrict O =
      ((μ.restrict V).withDensity jF).map full := by
    rw [source.graph_parametric_volume μ hL slope,
      Measure.restrict_map_of_aemeasurable fullMeasurable.aemeasurable openO.measurableSet,
      restrict_withDensity', Measure.restrict_restrict' (source.projection_open hL slope).measurableSet]
    rw [inter_comm, ← domain]
  rw [restricted, smallEmbedded.graph_parametric_volume μ hL smallSlope]
  exact (maps.trans (congrArg (fun ν => ν.map full) weights)).symm
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
