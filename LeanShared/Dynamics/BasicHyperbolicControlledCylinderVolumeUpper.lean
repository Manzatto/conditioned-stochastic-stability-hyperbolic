module

public import LeanShared.Dynamics.BasicHyperbolicExactFiniteShooting
public import LeanShared.Dynamics.LocalFiniteBoundaryCylinderVolumeUpper
public import LeanShared.Dynamics.FiniteHyperbolicReferenceJacobian
public import LeanShared.Geometry.CoherentCenteredDecodeBounds

/-! Actual hyperbolic basic data construct finite orbit cylinders with a
single positive endpoint radius, uniform in length and reference point,
and volume upper controlled by the literal unstable-Jacobian product. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ContDiff Bundle NNReal BigOperators
open CoherentCenteredCoordinateMaps

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_controlled_cylinder_upper_volume
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (γ : ℝ) (hγ : 1 < γ) (ε : ℝ) (positiveε : 0 < ε) :
    ∃ a : IsometricFraming b.hyperbolic, ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 < B ∧
      (∀ x : Λ, ‖(a.whole x).toContinuousLinearMap‖ ≤ B ∧
        ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ B) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ d : CompactCoherentCenteredCharts.Data (E := E)
        (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        ((T^N : M ≃ₜ M) : M → M) Λ B δ,
      ∃ preserves : MapsTo ((T^N : M ≃ₜ M) : M → M) Λ Λ, ∃ r : ℝ, 0 < r ∧
      ∀ p : ℕ, 0 < p → ∀ x : Λ, ∃ q : FiniteBoundaryHyperbolicTransform.Data
        (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)) p,
        (∀ i z, ‖z‖ ≤ d.radius → q.map i z =
          localMap d a.whole preserves (b.hyperbolic.iteratePoint (N * i.val) x) z) ∧
        (∀ z ∈ q.shooting ⁻¹' ball 0 r, ∀ j ≤ p, ‖q.evolve z j‖ < d.radius) ∧
        (∀ z ∈ q.shooting ⁻¹' ball 0 r, ∀ j ≤ p,
          dist (decode d a.whole (b.hyperbolic.iteratePoint (N * j) x) (q.evolve z j))
            (b.hyperbolic.iteratePoint (N * j) x).val < ε) ∧
        ∀ μ : Measure (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)),
          ∀ [IsAddHaarMeasure μ],
            ENNReal.ofReal (∏ j ∈ Finset.range (N * p),
              b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) *
                μ (q.shooting ⁻¹' ball 0 r) ≤ ENNReal.ofReal (γ ^ p) * μ (ball 0 r) := by
  obtain ⟨a⟩ := b.exists_isometricFraming (forward.mdifferentiable one_ne_zero)
    (inverse.mdifferentiable one_ne_zero)
  obtain ⟨η, positiveη, volume⟩ := LocalFiniteBoundaryCylinderVolumeUpper.exists_radius
    (U := EuclideanSpace ℝ (Fin a.unstableDimension))
    (S := EuclideanSpace ℝ (Fin a.stableDimension)) γ hγ
  let δ := min (η / 4) (1 / 32)
  have positiveδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have smallδ : δ ≤ 1 / 32 := min_le_right _ _
  have deltaBound : δ * 2 ≤ η := by
    have small : δ ≤ η / 4 := min_le_left _ _
    linarith
  have small : (1 / 4 : ℝ≥0) + δ.toNNReal * 2 < 1 := by
    change (1 / 4 : ℝ) + (δ.toNNReal : ℝ) * 2 < 1
    rw [Real.coe_toNNReal δ positiveδ.le]
    linarith
  obtain ⟨N, positiveN, blocks⟩ := b.hyperbolic.exists_blocks_in_coherent_frames
    (P := EuclideanSpace ℝ (Fin a.stableDimension))
    (Q := EuclideanSpace ℝ (Fin a.unstableDimension))
    (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero)
    (1 / 4) (by norm_num)
  obtain ⟨B, positiveB, frames⟩ := a.exists_uniform_bound
  let H := ((T^N : M ≃ₜ M) : M → M)
  have iterateSmooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H := by
    rw [show H = T^[N] from DiffeomorphismIterates.coe_pow T N]
    exact forward.iterate N
  obtain ⟨d⟩ := CompactCoherentCenteredCharts.exists_data
    (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
    (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
    H iterateSmooth Λ b.hyperbolic.compact B δ positiveB positiveδ
  have preserves : MapsTo H Λ Λ := by
    have step : MapsTo T Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
    intro x hx
    rw [show H = T^[N] from DiffeomorphismIterates.coe_pow T N]
    exact step.iterate N hx
  choose S U boundS boundU actionS actionU inverseAction using
    (fun x => blocks a.stable a.unstable x)
  have linearization (x : Λ) :
      (a.whole (advance preserves x)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
      (U x).toContinuousLinearMap.prodMap (S x).toContinuousLinearMap := by
    let targetFrame :
        (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) ≃L[ℝ]
          TangentSpace (𝓘(ℝ, E)) (H x.val) := a.whole (advance preserves x)
    apply ContinuousLinearMap.ext
    intro z
    change targetFrame.symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val (a.whole x z)) = _
    apply targetFrame.injective
    rw [targetFrame.apply_symm_apply]
    change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val (a.whole x z) =
      a.whole (advance preserves x) (U x z.1, S x z.2)
    have target : advance preserves x = b.hyperbolic.iteratePoint N x := Subtype.ext rfl
    rw [target, a.whole_apply, a.whole_apply, map_add]
    exact congrArg₂ (fun v w => v + w) (actionU x z.1).symm (actionS x z.2).symm
  obtain ⟨ρ, positiveρ, near⟩ := exists_decode_radius d a.whole positiveB frames ε positiveε
  let R := min d.radius ρ
  have positiveSmallRadius : 0 < R := lt_min d.positive positiveρ
  let r := (1 - (1 / 4 + δ * 2)) * R
  have positiveR : 0 < r := mul_pos (by linarith) positiveSmallRadius
  refine ⟨a, N, positiveN, B, positiveB, frames, δ, positiveδ, d, preserves, r, positiveR, fun p hp x => ?_⟩
  let reference := fun i : Fin p => b.hyperbolic.iteratePoint (N * i.val) x
  let maps := fun i : Fin p => localMap d a.whole preserves (reference i)
  have differentiable (i : Fin p) (z) (hz : ‖z‖ ≤ d.radius) : DifferentiableAt ℝ (maps i) z :=
    (localMap_estimates d a.whole preserves (fun x => (frames x).1)
      (fun x => (frames x).2) (reference i) z hz).1
  have derivative (i : Fin p) (z) (hz : ‖z‖ ≤ d.radius) :
      ‖fderiv ℝ (maps i) z -
        (U (reference i)).toContinuousLinearMap.prodMap (S (reference i)).toContinuousLinearMap‖ ≤
        (δ.toNNReal : ℝ) := by
    have estimate := (localMap_estimates d a.whole preserves (fun x => (frames x).1)
      (fun x => (frames x).2) (reference i) z hz).2
    rw [linearization] at estimate
    simpa only [Real.coe_toNNReal δ positiveδ.le] using estimate.le
  obtain ⟨q, hA, hB, hk, hδ, agreement⟩ := LocalFiniteBoundaryShootingBlocks.construct p maps
    (fun i => U (reference i)) (fun i => (S (reference i)).toContinuousLinearMap)
    (1 / 4) δ.toNNReal small (fun i => boundU _) (fun i => boundS _)
    d.radius d.positive differentiable derivative (fun i => localMap_zero d a.whole preserves _)
  have boundary (v : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
      (hv : v ∈ ball 0 r) : ‖v‖ < (1 - (q.k + q.δ : ℝ≥0)) * R := by
    have member : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
    rw [hk, hδ]
    change ‖v‖ < (1 - (1 / 4 + (δ.toNNReal : ℝ) * 2)) * R
    rw [Real.coe_toNNReal δ positiveδ.le]
    exact member
  have tube (z) (hz : z ∈ q.shooting ⁻¹' ball 0 r) (j) (hj : j ≤ p) : ‖q.evolve z j‖ < R :=
    q.shooting_tube z R (boundary _ hz) j hj
  refine ⟨q, agreement, fun z hz j hj => (tube z hz j hj).trans_le (min_le_left _ _),
    fun z hz j hj => (near _ _ ((tube z hz j hj).le.trans (min_le_right _ _))).2, fun μ _ => ?_⟩
  have determinant : (∏ i : Fin p, |(q.expanding i).toLinearMap.det|) =
      ∏ j ∈ Finset.range (N * p), b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val) := by
    apply a.finite_reference_product (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) N p x preserves q
    intro i z
    rw [hA, hB]
    exact congrArg (fun L => L z) (linearization (reference i))
  have qDelta : (q.δ : ℝ) ≤ η := by
    rw [hδ]
    change (δ.toNNReal : ℝ) * 2 ≤ η
    rw [Real.coe_toNNReal δ positiveδ.le]
    exact deltaBound
  have result := volume p hp q (by rw [hk]; norm_num) qDelta maps R
    (fun i z hz => agreement i z (hz.le.trans (min_le_left _ _)))
    (fun i z hz => differentiable i z (hz.le.trans (min_le_left _ _)))
    μ (ball 0 r) measurableSet_ball boundary
  rw [determinant] at result
  exact result

end LeanShared.HyperbolicBasicSet
