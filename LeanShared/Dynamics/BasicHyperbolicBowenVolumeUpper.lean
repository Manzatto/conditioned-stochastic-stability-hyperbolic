module

public import LeanShared.Dynamics.BasicHyperbolicControlledCylinderVolumeUpper
public import LeanShared.Dynamics.CoherentFiniteOrbitEncoding
public import LeanShared.Geometry.CoherentCenteredCoordinateBounds
public import LeanShared.Geometry.CoherentCenteredReferenceVolumeUpper

/-! Upper smooth-reference volume for the actual finite Bowen ball. Every
tracking point is encoded in the constructed shooting cylinder; the radius
and volume constant are chosen before the orbit length and core point. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ContDiff Bundle NNReal ENNReal BigOperators
open CoherentCenteredCoordinateMaps

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_bowen_volume_upper
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
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ p : ℕ, 0 < p → ∀ x : Λ,
        ENNReal.ofReal (∏ j ∈ Finset.range (N * p),
          b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) *
          (referenceMeasure.measure μ) {y | ∀ j ≤ N * p,
            dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η} ≤
          C * ENNReal.ofReal (γ ^ p) := by
  obtain ⟨a, N, positiveN, B, positiveB, frameBounds, δ, positiveδ, d, preserves, r, positiveR, cylinders⟩ :=
    b.exists_controlled_cylinder_upper_volume forward inverse γ hγ 1 zero_lt_one
  let x₀ : Λ := ⟨b.nonempty.choose, b.nonempty.choose_spec⟩
  obtain ⟨ρ, positiveρ, Cv, finiteCv, volumeComparison⟩ := exists_reference_volume_upper_bound
    d a.whole positiveB frameBounds referenceMeasure μ x₀
  let θ := min ρ (min r d.radius)
  have positiveθ : 0 < θ := lt_min positiveρ (lt_min positiveR d.positive)
  obtain ⟨η, positiveη, coordinates⟩ := exists_coordinate_radius
    d a.whole positiveB frameBounds θ positiveθ
  let ν := μ.map (linear d a.whole x₀).symm
  refine ⟨N, positiveN, Cv * ν (ball 0 r),
    ENNReal.mul_ne_top finiteCv measure_ball_ne_top, η, positiveη, fun p hp x => ?_⟩
  obtain ⟨q, agreement, _tube, _tracking, volume⟩ := cylinders p hp x
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
  let W := {y | ∀ j ≤ N * p, dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η}
  have near (y : M) (hy : y ∈ W) (j : ℕ) (hj : j ≤ p) :
      ((T^N : M ≃ₜ M) : M → M)^[j] y ∈ (chart d (points ⟨j, by omega⟩)).source ∧
      ‖coordinate d a.whole (points ⟨j, by omega⟩)
        (((T^N : M ≃ₜ M) : M → M)^[j] y)‖ < θ := by
    apply coordinates
    change dist (((T^N : M ≃ₜ M) : M → M)^[j] y) ((T^(N*j)) x.val) < η
    simpa only [DiffeomorphismIterates.coe_pow, ← Function.iterate_mul] using
      hy (N*j) (Nat.mul_le_mul_left N hj)
  let cylinder := q.shooting ⁻¹' ball 0 r ∩ ball 0 ρ
  have openCylinder : IsOpen cylinder :=
    (isOpen_ball.preimage q.shooting_continuous).inter isOpen_ball
  have contain : W ⊆ decode d a.whole x '' cylinder := by
    intro y hy
    have source := (near y hy 0 (Nat.zero_le p)).1
    rw [initial] at source
    let z := coordinate d a.whole x y
    refine ⟨z, ⟨?_, ?_⟩, decode_coordinate d a.whole x y source⟩
    · have evolve := CoherentFiniteOrbitEncoding.evolve_coordinate d a.whole preserves
        points steps q agreement y (fun j hj => (near y hy j hj).1)
        (fun j hj => (near y hy j hj).2.le.trans
          ((min_le_right ρ (min r d.radius)).trans (min_le_right r d.radius))) p le_rfl
      rw [initial] at evolve
      change dist (q.shooting z) 0 < r
      rw [dist_zero_right, FiniteBoundaryHyperbolicTransform.Data.shooting, Prod.norm_def, evolve]
      apply max_lt
      · exact (norm_fst_le (coordinate d a.whole (points ⟨p, Nat.lt_succ_self p⟩)
          (((T^N : M ≃ₜ M) : M → M)^[p] y))).trans_lt
          ((near y hy p le_rfl).2.trans_le
            ((min_le_right ρ (min r d.radius)).trans (min_le_left r d.radius)))
      · apply (norm_snd_le z).trans_lt
        have bound := (near y hy 0 (Nat.zero_le p)).2.trans_le
          ((min_le_right ρ (min r d.radius)).trans (min_le_left r d.radius))
        simpa only [initial, Function.iterate_zero_apply] using bound
    · exact mem_ball_zero_iff.mpr (by
        have bound := (near y hy 0 (Nat.zero_le p)).2.trans_le (min_le_left ρ (min r d.radius))
        simpa only [initial, Function.iterate_zero_apply] using bound)
  have comparison := volumeComparison x cylinder openCylinder inter_subset_right
  have smaller : ν cylinder ≤ ν (q.shooting ⁻¹' ball 0 r) := measure_mono inter_subset_left
  calc
    _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range (N*p),
        b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) *
        (referenceMeasure.measure μ) (decode d a.whole x '' cylinder) :=
      mul_le_mul' le_rfl (measure_mono contain)
    _ ≤ ENNReal.ofReal (∏ j ∈ Finset.range (N*p),
        b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) *
        (Cv * ν (q.shooting ⁻¹' ball 0 r)) :=
      mul_le_mul' le_rfl (comparison.trans (mul_le_mul' le_rfl smaller))
    _ = Cv * (ENNReal.ofReal (∏ j ∈ Finset.range (N*p),
        b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)) * ν (q.shooting ⁻¹' ball 0 r)) := by
      ac_rfl
    _ ≤ Cv * (ENNReal.ofReal (γ^p) * ν (ball 0 r)) := mul_le_mul' le_rfl (volume ν)
    _ = _ := by ac_rfl

end LeanShared.HyperbolicBasicSet
