module

public import LeanShared.Dynamics.HyperbolicCoherentNonlinearCharts
public import LeanShared.Geometry.CoherentCenteredMapDynamics
public import LeanShared.Dynamics.LocalFiniteBoundaryShootingBlocks
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! An arbitrarily small derivative error is available for actual finite two-boundary shooting
for every orbit segment, in a single uniform coherent finite atlas. No
chart, block, radius, or nonlinear contraction source is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_exact_finite_shooting_data
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (δ : ℝ) (positiveδ : 0 < δ) (smallδ : δ ≤ 1 / 16) :
    ∃ a : IsometricFraming b.hyperbolic, ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 < B ∧
      (∀ x : Λ, ‖(a.whole x).toContinuousLinearMap‖ ≤ B ∧
        ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ B) ∧
      ∃ d : CompactCoherentCenteredCharts.Data (E := E)
        (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        ((T^N : M ≃ₜ M) : M → M) Λ B δ,
      ∃ preserves : MapsTo ((T^N : M ≃ₜ M) : M → M) Λ Λ,
      ∀ p : ℕ, ∀ x : Λ, ∃ q : FiniteBoundaryHyperbolicTransform.Data
        (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)) p,
        q.k = (1 / 4 : ℝ≥0) ∧ q.δ = δ.toNNReal * 2 ∧
        (∀ i z, ‖z‖ ≤ d.radius → q.map i z =
          localMap d a.whole preserves (b.hyperbolic.iteratePoint (N * i.val) x) z) ∧
        ∀ i z, (a.whole (advance preserves (b.hyperbolic.iteratePoint (N * i.val) x))).symm
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M)
            (b.hyperbolic.iteratePoint (N * i.val) x).val
            (a.whole (b.hyperbolic.iteratePoint (N * i.val) x) z)) =
          (q.expanding i z.1, q.contracting i z.2) := by
  obtain ⟨a, N, positiveN, B, positiveB, frames, ⟨d⟩, blocks⟩ :=
    b.exists_coherent_nonlinear_charts forward inverse (1 / 4) δ (by norm_num) positiveδ
  let H := ((T^N : M ≃ₜ M) : M → M)
  have preserves : MapsTo H Λ Λ := by
    have step : MapsTo T Λ Λ := fun x hx => by
      rw [← b.hyperbolic.invariant]
      exact mem_image_of_mem T hx
    intro x hx
    rw [show H = T^[N] from DiffeomorphismIterates.coe_pow T N]
    exact step.iterate N hx
  choose S U boundS boundU actual using blocks
  have linearization (x : Λ) :
      (a.whole (advance preserves x)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
      (U x).toContinuousLinearMap.prodMap (S x).toContinuousLinearMap := by
    have same : advance preserves x = b.hyperbolic.iteratePoint N x := Subtype.ext rfl
    apply ContinuousLinearMap.ext
    intro z
    change (a.whole (advance preserves x)).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val (a.whole x z)) = (U x z.1, S x z.2)
    rw [same]
    exact actual x z
  refine ⟨a, N, positiveN, B, positiveB, frames, d, preserves, fun p x => ?_⟩
  let reference := fun i : Fin p => b.hyperbolic.iteratePoint (N * i.val) x
  have differentiable (i : Fin p) (z) (hz : ‖z‖ ≤ d.radius) :
      DifferentiableAt ℝ (localMap d a.whole preserves (reference i)) z :=
    (localMap_estimates d a.whole preserves (fun x => (frames x).1)
      (fun x => (frames x).2) (reference i) z hz).1
  have derivative (i : Fin p) (z) (hz : ‖z‖ ≤ d.radius) :
      ‖fderiv ℝ (localMap d a.whole preserves (reference i)) z -
        (U (reference i)).toContinuousLinearMap.prodMap (S (reference i)).toContinuousLinearMap‖ ≤
        (δ.toNNReal : ℝ) := by
    have estimate := (localMap_estimates d a.whole preserves (fun x => (frames x).1)
      (fun x => (frames x).2) (reference i) z hz).2
    rw [linearization] at estimate
    simpa only [Real.coe_toNNReal δ positiveδ.le] using estimate.le
  obtain ⟨q, hA, hB, hk, hδ, agreement⟩ := LocalFiniteBoundaryShootingBlocks.construct p
    (fun i => localMap d a.whole preserves (reference i))
    (fun i => U (reference i)) (fun i => (S (reference i)).toContinuousLinearMap)
    (1 / 4) δ.toNNReal
    (by
      change (1 / 4 : ℝ) + (δ.toNNReal : ℝ) * 2 < 1
      rw [Real.coe_toNNReal δ positiveδ.le]
      linarith) (fun i => boundU _) (fun i => boundS _)
    d.radius d.positive differentiable derivative (fun i => localMap_zero d a.whole preserves _)
  refine ⟨q, hk, hδ, agreement, fun i z => ?_⟩
  rw [hA, hB]
  exact congrArg (fun L => L z) (linearization (reference i))

end LeanShared.HyperbolicBasicSet
