module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafParallelGraphs
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAffineIntegrals

/-! The full fake-leaf integral bound controls actual parallel parameter
integrals. The graph and positive geometric constant come from the cone. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem exists_parallel_integral_control (U : Submodule ℝ E) (C : Set E)
    (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U) :
    ∃ L : U →L[ℝ] Uᗮ, 0 < GraphJacobian.density b L ∧
      (∀ v : Uᗮ, C1Embedded U (AffineGraphParameter.carrier U L v) ∧
        FakeLeafGeometry.leafError C (Module.finrank ℝ Uᗮ)
          (AffineGraphParameter.carrier U L v)=0) ∧
      ∀ (f : E → ℂ) (A : ℝ), Continuous f →
        (∀ Γ : Index U C, (∫ x, ‖f x‖ ∂inducedVolume U volume Γ.val) ≤ A) →
        ∀ v : Uᗮ, (∫ u : U, ‖f (AffineGraphParameter.point U L v u)‖) ≤
          A/GraphJacobian.density b L := by
  obtain ⟨L,graphs⟩ := exists_parallel_graphs U C cone
  have positive := IntrinsicGraphJacobian.density_positive U b L
  refine ⟨L,positive,graphs,fun f A continuous bounded v => ?_⟩
  have bound := bounded ⟨AffineGraphParameter.carrier U L v,graphs v⟩
  rw [integral_affineGraph U L v b volume (fun x => ‖f x‖) continuous.norm] at bound
  apply (le_div_iff₀ positive).mpr
  rwa [mul_comm]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
