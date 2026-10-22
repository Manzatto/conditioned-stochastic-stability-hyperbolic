module
public import LeanShared.Geometry.SupportedHolderChartNativeBound
public import LeanShared.Analysis.HolderInterpolation

/-! The actual supported chart realization is bounded into the native Holder
 graph, not merely into continuous functions. No completed-space norm
 comparison is assumed. -/
public noncomputable section
namespace LeanShared.SupportedHolderChartSpace
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {b : ℝ} (hb : 0 ≤ b) {K : Set E} (hK : IsCompact K)
    (e : OpenPartialHomeomorph M E) (target : K ⊆ e.target)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)

/-- Extension by zero in a genuine chart, with its native Holder norm. -/
def nativeRealization :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    space (a := b) K →L[ℂ] BoundedHolderSpace.graph M b := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  letI : SeminormedAddCommGroup (space (a := b) K) :=
    (inferInstance : NormedAddCommGroup (space (a := b) K)).toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (BoundedHolderSpace.graph M b) :=
    (inferInstance : NormedAddCommGroup (BoundedHolderSpace.graph M b)).toSeminormedAddCommGroup
  let C := Classical.choose (native_increment_bound hb hK e target he)
  have hC := (Classical.choose_spec (native_increment_bound hb hK e target he)).1
  have bound := (Classical.choose_spec (native_increment_bound hb hK e target he)).2
  let lift := BoundedHolderSpace.liftCore M b (realization hK e target).toLinearMap
    (fun v => ⟨C*‖v‖,bound v⟩)
  refine lift.mkContinuous (max 1 C) (fun v => ?_)
  have increment : ∀ x y, ‖BoundedHolderSpace.physical M b (lift v) x-
      BoundedHolderSpace.physical M b (lift v) y‖ ≤ (C*‖v‖)*dist x y^b := bound v
  have estimate := HolderInterpolation.graph_norm_le b (lift v) (mul_nonneg hC (norm_nonneg v)) increment
  have physical : BoundedHolderSpace.physical M b (lift v) = realization hK e target v := rfl
  rw [physical] at estimate
  exact estimate.trans ((max_le (by
    exact (norm_physical hK e target v).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 C) (norm_nonneg v))))
    (mul_le_mul_of_nonneg_right (le_max_right 1 C) (norm_nonneg v)))

/-- The bounded lift represents the literal chart extension. -/
theorem physical_nativeRealization (v : space (a := b) K) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    BoundedHolderSpace.physical M b (nativeRealization hb hK e target he v) =
      realization hK e target v := by
  unfold nativeRealization
  dsimp only
  rfl

end LeanShared.SupportedHolderChartSpace
