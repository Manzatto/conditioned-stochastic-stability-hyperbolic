module
public import LeanShared.Dynamics.BasicHyperbolicWeightedCylinderIntegral

/-! The actual cylinder integral controls the full separated partition,
including its supremum over every finite separated set. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal BigOperators
open ThermodynamicDefinitions

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_weighted_partition_integral_lower
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (g : M → ℝ) (continuous : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (γ : ℝ) (hγ : 1 < γ) :
    ∃ N : ℕ, 0 < N ∧ ∀ ξ : ℝ, 0 < ξ → ∀ ρ : ℝ, 0 < ρ →
      ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∃ v : ℝ, 0 < v ∧
      ∀ p : ℕ, 0 < p → ENNReal.ofReal v * ENNReal.ofReal (Real.exp (-ξ * (N * p))) *
          separatedPartitionSum T (b.hyperbolic.potential g) Λ (N * p) ρ ≤
        C * ENNReal.ofReal (γ ^ p) *
          ∫⁻ y, ENNReal.ofReal (∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y))
            ∂(referenceMeasure.measure μ) := by
  obtain ⟨N, positiveN, bound⟩ := b.exists_weighted_cylinder_integral_lower
    forward inverse referenceMeasure μ g continuous positive γ hγ
  refine ⟨N, positiveN, fun ξ positiveξ ρ positiveρ => ?_⟩
  obtain ⟨C, finiteC, v, positiveV, estimate⟩ := bound ξ positiveξ ρ positiveρ
  refine ⟨C, finiteC, v, positiveV, fun p hp => ?_⟩
  unfold separatedPartitionSum
  simp only [ENNReal.mul_iSup]
  exact iSup_le fun s => iSup_le fun hs => estimate p hp s hs

end LeanShared.HyperbolicBasicSet
