module
public import LeanShared.Dynamics.HyperbolicIsometricFraming
public import LeanShared.Geometry.CompactCoherentCenteredCharts
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Coherent nonlinear centered charts are produced from the actual compact
hyperbolic basic set. Dimensions, coherent isometric frames, frame bounds,
one finite chart cover used at BOTH ends of each orbit step, one nonlinear radius, and the actual block diagonal
linear part are all derived. Continuous Riemannian geometry is explicit. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_coherent_nonlinear_charts
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (κ δ : ℝ) (positiveκ : 0 < κ) (positiveδ : 0 < δ) :
    ∃ a : IsometricFraming b.hyperbolic, ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 < B ∧
      (∀ x : Λ, ‖(a.whole x).toContinuousLinearMap‖ ≤ B ∧
        ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ B) ∧
      Nonempty (CompactCoherentCenteredCharts.Data (E := E)
        (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        ((T^N : M ≃ₜ M) : M → M) Λ B δ) ∧
      ∀ x : Λ,
        ∃ S : EuclideanSpace ℝ (Fin a.stableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
        ∃ U : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension),
          ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
          ∀ z, (a.whole (b.hyperbolic.iteratePoint N x)).symm
            (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x.val (a.whole x z)) =
              (U z.1, S z.2) := by
  obtain ⟨a⟩ := b.exists_isometricFraming (forward.mdifferentiable one_ne_zero)
    (inverse.mdifferentiable one_ne_zero)
  obtain ⟨N, positiveN, blocks⟩ := b.hyperbolic.exists_blocks_in_coherent_frames
    (P := EuclideanSpace ℝ (Fin a.stableDimension))
    (Q := EuclideanSpace ℝ (Fin a.unstableDimension))
    (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero) κ positiveκ
  obtain ⟨B, positiveB, frameBounds⟩ := a.exists_uniform_bound
  have iterateSmooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1
      ((T^N : M ≃ₜ M) : M → M) := by
    rw [DiffeomorphismIterates.coe_pow]
    exact forward.iterate N
  have charts := CompactCoherentCenteredCharts.exists_data
    (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
    (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
    ((T^N : M ≃ₜ M) : M → M) iterateSmooth Λ b.hyperbolic.compact B δ positiveB positiveδ
  refine ⟨a, N, positiveN, B, positiveB, frameBounds, charts, fun x => ?_⟩
  obtain ⟨S, U, boundS, boundU, actionS, actionU, _⟩ := blocks a.stable a.unstable x
  refine ⟨S, U, boundS, boundU, fun z => ?_⟩
  let targetFrame :
      (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) ≃L[ℝ]
        TangentSpace (𝓘(ℝ, E)) ((T^N) x.val) := a.whole (b.hyperbolic.iteratePoint N x)
  change targetFrame.symm
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x.val (a.whole x z)) = _
  apply targetFrame.injective
  rw [targetFrame.apply_symm_apply]
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x.val (a.whole x z) =
    a.whole (b.hyperbolic.iteratePoint N x) (U z.1, S z.2)
  rw [a.whole_apply, a.whole_apply, map_add]
  exact congrArg₂ (fun v w => v + w) (actionU z.1).symm (actionS z.2).symm

end LeanShared.HyperbolicBasicSet
