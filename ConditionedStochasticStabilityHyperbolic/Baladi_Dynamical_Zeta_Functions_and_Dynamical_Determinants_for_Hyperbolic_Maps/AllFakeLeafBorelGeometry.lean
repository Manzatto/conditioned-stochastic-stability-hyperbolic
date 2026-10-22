module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
public import LeanShared.Geometry.ChartedSubsetBorel

/-! Discharge the Borel-set premise of the actual fake-leaf model. -/
public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Embedded C¹ leaves are Borel by their actual locally compact atlas. -/
theorem C1Embedded.measurableSet {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) : MeasurableSet Γ := by
  obtain ⟨atlas, _⟩ := embedded
  let : ChartedSpace U Γ := atlas
  exact ChartedSubsetBorel.measurableSet_of_charted (H := U) Γ

/-- Borel leaf measurability is a proved output, so geometry sources need
only the projection-open and graph-area facts. -/
theorem ClassicalGeometry.of_projection_area
    (U : Submodule ℝ E) (μ : Measure U)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U)
    (projectionOpen : ∀ Γ : Set E, C1Embedded U Γ → ∀ L : ℝ, 0 ≤ L →
      (∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖) →
      IsOpen (FakeLeafGraph.parameterDomain U Γ))
    (area : ∀ (Γ : Set E) (embedded : C1Embedded U Γ) (L : ℝ) (hL : 0 ≤ L)
      (slope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖),
      (FakeLeafGraph.asGraphLeaf U Γ hL slope embedded.measurableSet b
        (projectionOpen Γ embedded L hL slope)).measure μ = inducedVolume U μ Γ) :
    ClassicalGeometry U μ b where
  borel := fun _ h => h.measurableSet
  projection_open := projectionOpen
  area := area

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
