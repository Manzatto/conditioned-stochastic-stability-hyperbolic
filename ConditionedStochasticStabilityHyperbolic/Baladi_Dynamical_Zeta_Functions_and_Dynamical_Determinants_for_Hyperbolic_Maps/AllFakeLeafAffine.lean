module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
public import LeanShared.Geometry.AffineSubspaceEmbedded
public import LeanShared.Analysis.FakeLeafFlatCondition
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import Lean.Elab.Tactic.Omega

/-! The full literal fake-leaf family contains every translated admissible
orthogonal plane. Their charts and immersion properties are constructed. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem affine_orthogonal_member (U : Submodule ℝ E) (C : Set E)
    (positive : 0 < Module.finrank ℝ Uᗮ) (P : Submodule ℝ E)
    (admissible : P ∈ FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ)) (a : E) :
    C1Embedded U ((fun v : Pᗮ => (v:E)+a) '' univ) ∧
      FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ)
        ((fun v : Pᗮ => (v:E)+a) '' univ)=0 := by
  have sameDimension : Module.finrank ℝ U=Module.finrank ℝ Pᗮ := by
    have hu := U.finrank_add_finrank_orthogonal
    have hp := P.finrank_add_finrank_orthogonal
    have dimensions := admissible.2
    omega
  let e : U ≃L[ℝ] Pᗮ := ContinuousLinearEquiv.ofFinrankEq sameDimension
  exact ⟨AffineSubspaceEmbedded.embedded U Pᗮ e a,
    FakeLeafGeometry.leafError_affine_orthogonal positive P admissible a⟩

@[expose] def affineLeaf (U : Submodule ℝ E) (C : Set E)
    (positive : 0 < Module.finrank ℝ Uᗮ) (P : Submodule ℝ E)
    (admissible : P ∈ FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ))
    (a : E) : Index U C :=
  ⟨((fun v : Pᗮ => (v:E)+a) '' univ),affine_orthogonal_member U C positive P admissible a⟩
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
