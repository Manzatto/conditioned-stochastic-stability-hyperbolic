module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProjectionOpen
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph
public import LeanShared.Geometry.ManifoldChordFullRank
public import LeanShared.Geometry.ManifoldLocalLeftInverse

/-! C¹ regularity of the actual inverse graph on its genuine projection domain. -/
public noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem C1Embedded.heightExtension_contDiffOn {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    ContDiffOn ℝ 1 (FakeLeafGraph.heightExtension U Γ hL slope)
      (FakeLeafGraph.parameterDomain U Γ) := by
  classical
  have domainOpen := embedded.projection_open hL slope
  obtain ⟨atlas, manifold, smooth, immersion⟩ := embedded
  let : ChartedSpace U Γ := atlas
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := manifold
  let p : Γ → U := FakeLeafGraph.projection U Γ
  have ps : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 p :=
    U.orthogonalProjectionOnto.contDiff.comp_contMDiff smooth
  intro u hu
  let x : Γ := FakeLeafGraph.point U Γ hL slope ⟨u, hu⟩
  have px : p x = u := FakeLeafGraph.point_projection U Γ hL slope ⟨u, hu⟩
  let branch : U → Γ := fun v => if hv : v ∈ FakeLeafGraph.parameterDomain U Γ then
    FakeLeafGraph.point U Γ hL slope ⟨v, hv⟩ else x
  have inverse : ∀ y : Γ, branch (p y) = y := by
    intro y
    have hy : p y ∈ FakeLeafGraph.parameterDomain U Γ := ⟨y, rfl⟩
    simp only [branch, dite_eq_left hy]
    exact FakeLeafGraph.point_of_projection U Γ hL slope y
  have rank := ManifoldChordFullRank.bijective_of_chord
    (smooth.contMDiffAt (x := x)) (ps.contMDiffAt (x := x)) (immersion x)
    (C := (Real.toNNReal (1 + L) : ℝ))
    (Filter.Eventually.of_forall (fun y : Γ => by
      change ‖(y : E) - (x : E)‖ ≤ (Real.toNNReal (1 + L) : ℝ) *
        ‖U.orthogonalProjectionOnto (y : E) - U.orthogonalProjectionOnto (x : E)‖
      simpa only [Subtype.dist_eq, dist_eq_norm] using
        (ConeGraphGeometry.leafProjection_antilipschitz U hL slope).le_mul_dist y x))
  have inverseRegular := ManifoldLocalLeftInverse.contMDiffAt_of_eventually_leftInverse
    (ps.contMDiffAt (x := x)) rank (Filter.Eventually.of_forall inverse)
  have ambientRegular : ContDiffAt ℝ 1 (fun v => (branch v : E)) u := by
    rw [← px]
    exact contMDiffAt_iff_contDiffAt.mp
      (smooth.contMDiffAt.comp (p x) inverseRegular)
  have heightRegular := Uᗮ.orthogonalProjectionOnto.contDiff.contDiffAt.comp u ambientRegular
  have agrees : FakeLeafGraph.heightExtension U Γ hL slope =ᶠ[𝓝 u]
      (fun v => Uᗮ.orthogonalProjectionOnto (branch v : E)) := by
    filter_upwards [domainOpen.mem_nhds hu] with v hv
    rw [FakeLeafGraph.heightExtension_on_domain U Γ hL slope ⟨v, hv⟩]
    simp only [FakeLeafGraph.height, branch, dite_eq_left hv]
  exact (heightRegular.congr_of_eventuallyEq agrees).contDiffWithinAt
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
