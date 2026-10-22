module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntrinsicArea
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImmersionAtlas
import all LeanShared.Geometry.EmbeddedSubmanifoldVolume
import all LeanShared.Analysis.GraphLeafNorm
import all LeanShared.Analysis.FakeLeafGraph

/-! Area identification for the independently chosen embedded-manifold volume. -/
public noncomputable section
open Set MeasureTheory Measure
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem C1Embedded.constructed_area {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) (μ : Measure U) [IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U)
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    (FakeLeafGraph.asGraphLeaf U Γ hL slope embedded.measurableSet b
      (embedded.projection_open hL slope)).measure μ =
      EmbeddedSubmanifoldVolume.volume U μ Γ := by
  classical
  by_cases nonempty : Nonempty Γ
  · let : Nonempty Γ := nonempty
    have independent := EmbeddedSubmanifoldVolume.volume_eq_map_data
      (show EmbeddedSubmanifoldVolume.Embedded U Γ from embedded) μ
    rw [independent]
    exact ((embedded.volumeData).intrinsic_area μ b hL slope).symm
  · have emptyΓ : Γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact nonempty ⟨⟨x, hx⟩⟩
    have domain : FakeLeafGraph.parameterDomain U Γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro u ⟨x, _⟩
      exact nonempty ⟨x⟩
    have zeroVolume : EmbeddedSubmanifoldVolume.volume U μ Γ = 0 := by
      simp only [EmbeddedSubmanifoldVolume.volume,
        dite_eq_left (show EmbeddedSubmanifoldVolume.Embedded U Γ from embedded),
        EmbeddedSubmanifoldVolume.intrinsic, dite_eq_right nonempty, Measure.map_zero]
    rw [zeroVolume]
    change Measure.map _ ((μ.restrict (FakeLeafGraph.parameterDomain U Γ)).withDensity _) = 0
    rw [domain, Measure.restrict_empty, withDensity_zero_left, Measure.map_zero]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
