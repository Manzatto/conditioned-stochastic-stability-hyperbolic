module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProjectionAtlas
public import LeanShared.MeasureTheory.ImmersionAtlasExtraChart
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The independently constructed induced volume has the actual intrinsic
Jacobian in the global graph projection coordinates. -/
public noncomputable section
open Set MeasureTheory Measure IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem EmbeddedVolumeAtlas.intrinsicMeasure_eq_projection {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (data : EmbeddedVolumeAtlas U Γ) (μ : Measure U) [IsAddHaarMeasure μ]
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    let e := FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope)
    data.intrinsicMeasure μ = CoordinatePatchMeasure.patch e μ
      (IntrinsicCoordinatePatchMeasures.density (Subtype.val ∘ e.symm) e.target) := by
  let : ChartedSpace U Γ := data.charted
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := data.manifold
  let e := FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope)
  have member : e ∈ maximalAtlas (𝓘(ℝ, U)) 1 Γ := data.projection_mem_maximalAtlas hL slope
  have globalSmooth : ContMDiffOn (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E) univ :=
    data.smooth.contMDiffOn
  have param : ContDiffOn ℝ 1 (Subtype.val ∘ e.symm) e.target :=
    (globalSmooth.comp (contMDiffOn_symm_of_mem_maximalAtlas member)
      (fun _ _ => mem_univ _)).contDiffOn
  have cross : ∀ n, ContDiffOn ℝ 1 ((data.model.chart n).symm.trans e)
      ((data.model.chart n).symm.trans e).source := by
    intro n
    have hi := contMDiffOn_symm_of_mem_maximalAtlas (data.compatible n)
    have he := contMDiffOn_of_mem_maximalAtlas member
    exact (he.comp (hi.mono (fun _ h => h.1)) (fun _ h => h.2)).contDiffOn
  have localVolume := ImmersionAtlasVolume.restrict_compatible_chart data.model μ e param cross
  change (data.intrinsicMeasure μ).restrict univ = _ at localVolume
  rwa [Measure.restrict_univ] at localVolume
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
