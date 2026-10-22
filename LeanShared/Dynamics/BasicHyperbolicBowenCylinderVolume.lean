module

public import LeanShared.Dynamics.BasicHyperbolicUniformManifoldCylinderVolume
public import LeanShared.Dynamics.BlockTrackingUniformity

/-! The actual positive-volume cylinders track the literal orbit at EVERY
one-step time, including both endpoints. The block length is fixed before
the requested tracking accuracy. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal BigOperators

set_option maxHeartbeats 2000000 in
theorem BasicData.exists_bowen_cylinder_volume
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (γ : ℝ) (hγ : 1 < γ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ] :
    ∃ N : ℕ, 0 < N ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∃ v : ℝ, 0 < v ∧
      ∀ p : ℕ, 0 < p → ∀ x : Λ, ∃ W : Set M, IsOpen W ∧
        (∀ y ∈ W, ∀ j ≤ N * p, dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < ε) ∧
        ENNReal.ofReal v ≤ C * ENNReal.ofReal (γ ^ p * ∏ j ∈ Finset.range (N * p),
          b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) * (referenceMeasure.measure μ) W := by
  obtain ⟨N, positiveN, cylinders⟩ := b.exists_uniform_manifold_cylinder_volume
    forward inverse γ hγ referenceMeasure μ
  refine ⟨N, positiveN, fun ε positiveε => ?_⟩
  obtain ⟨η, positiveη, tracking⟩ := BlockTrackingUniformity.exists_tolerance
    (T : M → M) T.continuous N positiveN ε positiveε
  obtain ⟨C, finiteC, v, positiveV, sets⟩ := cylinders η positiveη
  refine ⟨C, finiteC, v, positiveV, fun p hp x => ?_⟩
  obtain ⟨W, openW, blocks, volume⟩ := sets p hp x
  exact ⟨W, openW, fun y hy => tracking p y x.val (blocks y hy), volume⟩

end LeanShared.HyperbolicBasicSet
