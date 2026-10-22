module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImmersionAtlas
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProjectionOpen
public import LeanShared.Analysis.FakeLeafProjectionChart
public import LeanShared.Geometry.ManifoldChordFullRank
public import LeanShared.Geometry.ManifoldLocalLeftInverse
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph

/-! The actual global graph projection belongs to the independently chosen
C¹ leaf atlas. This connects the intrinsic volume construction to graph
coordinates without defining the volume by the graph. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem EmbeddedVolumeAtlas.embedded {U : Submodule ℝ E} {Γ : Set E}
    (data : EmbeddedVolumeAtlas U Γ) : C1Embedded U Γ :=
  ⟨data.charted, data.manifold, data.smooth, data.immersion⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem EmbeddedVolumeAtlas.projection_mem_maximalAtlas {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (data : EmbeddedVolumeAtlas U Γ) {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    letI := data.charted
    FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope) ∈
      maximalAtlas (𝓘(ℝ, U)) 1 Γ := by
  let : ChartedSpace U Γ := data.charted
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := data.manifold
  let p : Γ → U := FakeLeafGraph.projection U Γ
  let inv : U → Γ := FakeLeafProjectionChart.inversePoint U Γ hL slope
  have ps : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 p :=
    U.orthogonalProjectionOnto.contDiff.comp_contMDiff data.smooth
  have inverseRegular : ContMDiffOn (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 inv
      (FakeLeafGraph.parameterDomain U Γ) := by
    intro u hu
    let x : Γ := inv u
    have px : p x = u := FakeLeafProjectionChart.projection_inverse U Γ hL slope u hu
    have rank := ManifoldChordFullRank.bijective_of_chord
      (data.smooth.contMDiffAt (x := x)) (ps.contMDiffAt (x := x)) (data.immersion x)
      (C := (Real.toNNReal (1 + L) : ℝ))
      (Filter.Eventually.of_forall (fun y : Γ => by
        change ‖(y : E) - (x : E)‖ ≤ (Real.toNNReal (1 + L) : ℝ) *
          ‖U.orthogonalProjectionOnto (y : E) - U.orthogonalProjectionOnto (x : E)‖
        simpa only [Subtype.dist_eq, dist_eq_norm] using
          (ConeGraphGeometry.leafProjection_antilipschitz U hL slope).le_mul_dist y x))
    have regular := ManifoldLocalLeftInverse.contMDiffAt_of_eventually_leftInverse
      (ps.contMDiffAt (x := x)) rank
      (Filter.Eventually.of_forall (FakeLeafProjectionChart.inverse_projection U Γ hL slope))
    rw [px] at regular
    exact regular.contMDiffWithinAt
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  exact ⟨ps.contMDiffOn, inverseRegular⟩
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
