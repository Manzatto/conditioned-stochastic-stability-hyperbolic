module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAffine
public import LeanShared.Geometry.ProjectionComplementGraph
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import Lean.Elab.Tactic.Omega

/-! The literal cone hypotheses produce one actual linear graph whose full
parallel translates all belong to the paper's full fake-leaf family. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_parallel_graphs (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) :
    ∃ L : U →L[ℝ] Uᗮ, ∀ v : Uᗮ,
      C1Embedded U (AffineGraphParameter.carrier U L v) ∧
      FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ)
        (AffineGraphParameter.carrier U L v)=0 := by
  classical
  obtain ⟨P,admissible⟩ := cone.normal_planes
  let Γ := affineLeaf U C cone.stable_positive P admissible (0:E)
  have belongs (p : Pᗮ) : (p:E) ∈ Γ.val := by
    exact ⟨p,mem_univ _,add_zero _⟩
  let A := U.orthogonalProjectionOnto.comp Pᗮ.subtypeL
  have injective : Function.Injective A := by
    intro p q hpq
    have inj := FakeLeafGraph.projection_injective U Γ.val
      (slope_positive U C cone).le (slope_bound U C cone Γ)
    have same : (⟨(p:E),belongs p⟩ : Γ.val)=⟨(q:E),belongs q⟩ := inj hpq
    exact Subtype.ext (congrArg (fun x : Γ.val => (x:E)) same)
  have dimension : Module.finrank ℝ Pᗮ=Module.finrank ℝ U := by
    have hu := U.finrank_add_finrank_orthogonal
    have hp := P.finrank_add_finrank_orthogonal
    have dimensions := admissible.2
    omega
  obtain ⟨L,equality⟩ := ProjectionComplementGraph.exists_graph U Pᗮ dimension injective
  refine ⟨L,fun v => ?_⟩
  rw [equality v]
  exact affine_orthogonal_member U C cone.stable_positive P admissible (v:E)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
