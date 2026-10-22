module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafGraphRegularity
public import LeanShared.Analysis.SecantProjectionDerivative
public import LeanShared.Analysis.TransverseSubspaceJacobian
import all LeanShared.Analysis.FakeLeafGraph

/-! Actual leaf tangents inherit the SAME secant-cone projection bound,
also when the comparison plane is the varying genuine unstable fiber. -/
public noncomputable section
open Set
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem C1Embedded.tangent_projection_slope {V : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded V Γ) {L : ℝ} (hL : 0 ≤ L)
    (sourceSlope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Vᗮ.starProjection (x-y)‖ ≤ L * ‖V.starProjection (x-y)‖)
    (U : Submodule ℝ E) (K : ℝ)
    (secants : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ K * ‖U.starProjection (x-y)‖)
    (u : V) (hu : u ∈ FakeLeafGraph.parameterDomain V Γ) :
    let g := ConeGraphGeometry.graphPoint V (FakeLeafGraph.heightExtension V Γ hL sourceSlope)
    ∀ w : (fderiv ℝ g u).toLinearMap.range,
      ‖Uᗮ.orthogonalProjectionOnto (w : E)‖ ≤ K * ‖U.orthogonalProjectionOnto (w : E)‖ := by
  intro g
  have domainOpen := embedded.projection_open hL sourceSlope
  have heightRegular := ((embedded.heightExtension_contDiffOn hL sourceSlope).differentiableOn
    one_ne_zero u hu).differentiableAt (domainOpen.mem_nhds hu)
  have derivative := V.subtypeL.hasFDerivAt.add
    (Vᗮ.subtypeL.hasFDerivAt.comp u heightRegular.hasFDerivAt)
  have differentiable : DifferentiableAt ℝ g u := derivative.differentiableAt
  have onLeaf (v : V) (hv : v ∈ FakeLeafGraph.parameterDomain V Γ) : g v ∈ Γ :=
    (FakeLeafGraph.graphExtension_image V Γ hL sourceSlope).subset ⟨v, hv, rfl⟩
  apply SecantProjectionDerivative.range_bound differentiable.hasFDerivAt
    (domainOpen.mem_nhds hu) U K
  intro v hv
  exact secants (g v) (onLeaf v hv) (g u) (onLeaf u hu)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
