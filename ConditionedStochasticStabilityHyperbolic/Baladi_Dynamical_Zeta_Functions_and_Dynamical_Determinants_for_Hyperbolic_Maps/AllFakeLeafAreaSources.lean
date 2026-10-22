module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProjectionOpen

/-! The original three-field geometry package needs only its graph-area identity: measurability and
projection openness are proved outputs. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ClassicalGeometry.of_area (U : Submodule ℝ E) (μ : Measure U)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U)
    (area : ∀ (Γ : Set E) (embedded : C1Embedded U Γ) (L : ℝ) (hL : 0 ≤ L)
      (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
        ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖),
      (FakeLeafGraph.asGraphLeaf U Γ hL slope embedded.measurableSet b
        (embedded.projection_open hL slope)).measure μ = inducedVolume U μ Γ) :
    ClassicalGeometry U μ b :=
  ClassicalGeometry.of_projection_area U μ b
    (fun _ embedded _ hL slope => embedded.projection_open hL slope) area
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
