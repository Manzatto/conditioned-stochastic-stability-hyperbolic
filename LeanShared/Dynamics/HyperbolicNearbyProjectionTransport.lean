module
public import LeanShared.Dynamics.HyperbolicProjectionCoordinates
public import LeanShared.Analysis.IntertwiningProjectionInverseBounds
public import LeanShared.Topology.CompactNearDiagonalContinuity
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual continuous hyperbolic splitting yields uniformly controlled
simultaneous stable/unstable transport between nearby reference points in a
fixed bundle chart. Arbitrary chosen split frames need not be continuous. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_uniform_projection_transport
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ, E)))))
    [e.IsLinear ℝ] (K : Set Λ) (compact : IsCompact K)
    (inside : ∀ x ∈ K, x.val ∈ e.baseSet) (θ : ℝ) (positive : 0 < θ) (small : θ < 1) :
    let P : Λ → E →L[ℝ] E := fun x => BundleEndomorphismCoordinates.coordinates
      (TangentSpace (𝓘(ℝ, E))) e h.projection x.val
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ y : Λ, dist x y < η →
      y.val ∈ e.baseSet ∧ ∃ R : E ≃L[ℝ] E,
        R.toContinuousLinearMap = IntertwiningProjectionTransport.transport (P x) (P y) ∧
        (P y).comp R.toContinuousLinearMap = R.toContinuousLinearMap.comp (P x) ∧
        ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ < θ ∧
        ‖R.toContinuousLinearMap‖ ≤ 1 + θ ∧
        ‖R.symm.toContinuousLinearMap‖ ≤ 1 / (1 - θ) := by
  intro P
  let U : Set Λ := Subtype.val ⁻¹' e.baseSet
  have openU : IsOpen U := e.open_baseSet.preimage continuous_subtype_val
  have continuous : ContinuousOn P U :=
    h.projection_coordinates_continuous e |>.comp continuous_subtype_val.continuousOn
      (fun x hx => ⟨x.property,hx⟩)
  obtain ⟨C,bounded⟩ := compact.exists_bound_of_continuousOn (continuous.mono inside)
  let B := max C 0
  have nonnegB : 0 ≤ B := le_max_right _ _
  have bound (x : Λ) (hx : x ∈ K) : ‖P x‖ ≤ B := (bounded x hx).trans (le_max_left _ _)
  have factor : 0 < 2 * B + 1 := by positivity
  obtain ⟨η,positiveη,close⟩ := CompactNearDiagonalContinuity.exists_radius K U compact openU
    inside P continuous (θ / (2 * B + 1)) (div_pos positive factor)
  refine ⟨η,positiveη,fun x hx y near => ?_⟩
  have facts := close x hx y near
  have idempotentX := h.projection_coordinates_idempotent e x.val ⟨x.property,inside x hx⟩
  have idempotentY := h.projection_coordinates_idempotent e y.val ⟨y.property,facts.1⟩
  have difference : ‖P x - P y‖ < θ / (2 * B + 1) := by
    simpa only [dist_eq_norm] using facts.2
  have control : ‖P x - P y‖ * (2 * ‖P x‖ + 1) < θ := calc
    _ ≤ ‖P x - P y‖ * (2 * B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [bound x hx]) (norm_nonneg _)
    _ < (θ / (2 * B + 1)) * (2 * B + 1) := mul_lt_mul_of_pos_right difference factor
    _ = θ := div_mul_cancel₀ _ (ne_of_gt factor)
  let R := IntertwiningProjectionTransport.equivalence (P x) (P y) idempotentX (control.trans small)
  have actual : R.toContinuousLinearMap = IntertwiningProjectionTransport.transport (P x) (P y) := rfl
  refine ⟨facts.1,R,actual,?_,?_,?_,?_⟩
  · rw [actual]
    exact IntertwiningProjectionTransport.commutes (P x) (P y) idempotentX idempotentY
  · rw [actual]
    exact (IntertwiningProjectionTransport.norm_sub_id_le (P x) (P y) idempotentX).trans_lt control
  · rw [actual]
    exact (IntertwiningProjectionTransport.norm_le (P x) (P y) idempotentX).trans (by linarith)
  · exact (IntertwiningProjectionTransport.inverse_norm_le (P x) (P y) idempotentX
      (control.trans small)).trans (one_div_le_one_div_of_le (sub_pos.mpr small) (by linarith))

end LeanShared.HyperbolicBasicSet
