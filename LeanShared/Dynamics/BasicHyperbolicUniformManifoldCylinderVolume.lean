module

public import LeanShared.Dynamics.BasicHyperbolicExactFiniteShooting
public import LeanShared.Dynamics.LocalFiniteBoundaryCylinderVolume
public import LeanShared.Dynamics.FiniteHyperbolicReferenceJacobian
public import LeanShared.Geometry.CoherentCenteredDecodeBounds
public import LeanShared.Geometry.CoherentCenteredReferenceVolume
public import LeanShared.Dynamics.CoherentFiniteOrbitDecoding

/-! Actual hyperbolic basic data construct finite orbit cylinders with a
single positive endpoint radius, uniform in length and reference point,
and volume lower controlled by the literal unstable-Jacobian product. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ContDiff Bundle NNReal ENNReal BigOperators
open CoherentCenteredCoordinateMaps

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_uniform_manifold_cylinder_volume
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (γ : ℝ) (hγ : 1 < γ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ] :
    ∃ N : ℕ, 0 < N ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∃ v : ℝ, 0 < v ∧
      ∀ p : ℕ, 0 < p → ∀ x : Λ, ∃ W : Set M, IsOpen W ∧
        (∀ y ∈ W, ∀ j ≤ p, dist ((T : M → M)^[N * j] y) ((T : M → M)^[N * j] x.val) < ε) ∧
        ENNReal.ofReal v ≤ C * ENNReal.ofReal (γ ^ p * ∏ j ∈ Finset.range (N * p),
          b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) * (referenceMeasure.measure μ) W := by
  obtain ⟨a⟩ := b.exists_isometricFraming (forward.mdifferentiable one_ne_zero)
    (inverse.mdifferentiable one_ne_zero)
  obtain ⟨η, positiveη, volume⟩ := LocalFiniteBoundaryCylinderVolume.exists_radius
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
  refine ⟨N, positiveN, fun ε positiveε => ?_⟩
  obtain ⟨ρ, positiveρ, near⟩ := exists_decode_radius d a.whole positiveB frames ε positiveε
  let x₀ : Λ := ⟨b.nonempty.choose, b.nonempty.choose_spec⟩
  obtain ⟨ρv, positiveρv, Cv, finiteCv, volumeConversion⟩ := exists_reference_volume_bound
    d a.whole positiveB frames referenceMeasure μ x₀
  let R := min d.radius (min ρ ρv)
  have positiveSmallRadius : 0 < R := lt_min d.positive (lt_min positiveρ positiveρv)
  let r := (1 - (1 / 4 + δ * 2)) * R
  have positiveR : 0 < r := mul_pos (by linarith) positiveSmallRadius
  let ν := μ.map (linear d a.whole x₀).symm
  let v := (ν (ball 0 r)).toReal
  have positiveV : 0 < v := ENNReal.toReal_pos (measure_ball_pos ν 0 positiveR).ne' measure_ball_ne_top
  refine ⟨Cv, finiteCv, v, positiveV, fun p hp x => ?_⟩
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
    ν (ball 0 r) measurableSet_ball boundary
  rw [determinant] at result
  let cylinder := q.shooting ⁻¹' ball 0 r
  let W := decode d a.whole x '' cylinder
  have openCylinder : IsOpen cylinder := isOpen_ball.preimage q.shooting_continuous
  have coordinateBound : cylinder ⊆ ball 0 ρv := by
    intro z hz
    have small := tube z hz 0 (Nat.zero_le p)
    change ‖z‖ < R at small
    exact mem_ball_zero_iff.mpr (small.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have comparison := volumeConversion x cylinder openCylinder coordinateBound
  have targetBound (z) (hz : z ∈ cylinder) :
      chart d x x.val + linear d a.whole x z ∈ (chart d x).target := by
    have small := tube z hz 0 (Nat.zero_le p)
    change ‖z‖ < R at small
    exact (near x z (small.le.trans ((min_le_right _ _).trans (min_le_left _ _)))).1
  let coordinateSet := (fun y => chart d x x.val + y) '' ((linear d a.whole x) '' cylinder)
  have openCoordinateSet : IsOpen coordinateSet := (Homeomorph.addLeft (chart d x x.val)).isOpenMap _
    ((linear d a.whole x).toHomeomorph.isOpenMap _ openCylinder)
  have targetSet : coordinateSet ⊆ (chart d x).target := by
    rintro y ⟨u, ⟨z, hz, rfl⟩, rfl⟩
    exact targetBound z hz
  have image : (chart d x).symm '' coordinateSet = W := by
    simp only [coordinateSet, Set.image_image]
    rfl
  have openW : IsOpen W := by
    rw [← image]
    exact (chart d x).isOpen_image_symm_of_subset_target openCoordinateSet targetSet
  refine ⟨W, openW, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩ j hj
    let points := fun i : Fin (p + 1) => b.hyperbolic.iteratePoint (N * i.val) x
    have initial : points ⟨0, Nat.zero_lt_succ p⟩ = x := by
      apply Subtype.ext
      change (T^(N * 0)) x.val = x.val
      rw [Nat.mul_zero, pow_zero]
      rfl
    have steps (i : Fin p) : advance preserves (points ⟨i.val, by omega⟩) =
        points ⟨i.val + 1, by omega⟩ := by
      apply Subtype.ext
      change (T^N * T^(N * i.val)) x.val = (T^(N * (i.val + 1))) x.val
      rw [← pow_add, Nat.mul_add, Nat.mul_one, Nat.add_comm N (N * i.val)]
    have actual := CoherentFiniteOrbitDecoding.decode_evolve d a.whole preserves
      (fun x => (frames x).1) (fun x => (frames x).2) points steps q
      (fun i w hw => agreement i w hw) z
      (fun k hk => (tube z hz k hk).le.trans (min_le_left _ _)) j hj
    rw [initial] at actual
    have nearPoint := (near (points ⟨j, by omega⟩) (q.evolve z j)
      ((tube z hz j hj).le.trans ((min_le_right _ _).trans (min_le_left _ _)))).2
    rw [actual] at nearPoint
    change dist (H^[j] (decode d a.whole x z)) ((T^(N * j)) x.val) < ε at nearPoint
    simpa only [H, DiffeomorphismIterates.coe_pow, ← Function.iterate_mul] using nearPoint
  · rw [ENNReal.ofReal_toReal measure_ball_ne_top]
    calc
      ν (ball 0 r) ≤ ENNReal.ofReal (γ ^ p * ∏ j ∈ Finset.range (N * p),
          b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) * ν cylinder := result
      _ ≤ ENNReal.ofReal (γ ^ p * ∏ j ∈ Finset.range (N * p),
          b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) *
          (Cv * (referenceMeasure.measure μ) W) := mul_le_mul' le_rfl comparison
      _ = _ := by rw [← mul_assoc, mul_comm _ Cv]

end LeanShared.HyperbolicBasicSet
