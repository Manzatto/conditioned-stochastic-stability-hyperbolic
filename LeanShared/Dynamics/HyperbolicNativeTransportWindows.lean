module
public import LeanShared.Dynamics.HyperbolicNearbyProjectionTransport
public import LeanShared.Geometry.ProjectionFiberTransport
public import LeanShared.Geometry.CompactRiemannianTrivializations
public import Mathlib.Tactic.Ring

/-! The metric neighborhood and native norm factor are chosen BEFORE the
requested coordinate error. Hence a hyperbolic iterate may be chosen first,
and the projection transport error may then be made arbitrarily small. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_native_transport_windows
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (center : Λ) :
    let e := trivializationAt E (fun x : M => TangentSpace (𝓘(ℝ, E)) x) center.val
    ∃ W : Set Λ, IsOpen W ∧ center ∈ W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K : Set Λ, IsCompact K → K ⊆ W →
      ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ y : Λ, dist x y < η →
        ∃ R : TangentSpace (𝓘(ℝ, E)) x.val ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val,
          (∀ v, h.projection y.val (R v) = R (h.projection x.val v)) ∧
          ‖R.toContinuousLinearMap‖ ≤ C ^ 2 * (1 + θ) ∧
          ‖R.symm.toContinuousLinearMap‖ ≤ C ^ 2 / (1 - θ) ∧
          ‖(e.continuousLinearMapAt ℝ y.val).comp
            (R.toContinuousLinearMap.comp (e.symmL ℝ x.val)) - ContinuousLinearMap.id ℝ E‖ < θ := by
  intro e
  let fibers := fun x : M => TangentSpace (𝓘(ℝ, E)) x
  obtain ⟨C,positiveC,nearby⟩ := CompactRiemannianTrivializations.local_bound
    (F := E) fibers center.val
  obtain ⟨O,contained,openO,member⟩ := mem_nhds_iff.mp nearby
  let W : Set Λ := Subtype.val ⁻¹' O
  have openW : IsOpen W := openO.preimage continuous_subtype_val
  have nativeBounds (x : Λ) (hx : x ∈ W) :
      x.val ∈ e.baseSet ∧ ‖e.continuousLinearMapAt ℝ x.val‖ ≤ C ∧ ‖e.symmL ℝ x.val‖ ≤ C :=
    contained hx
  refine ⟨W,openW,member,C,positiveC,fun θ positive small K compact inside => ?_⟩
  have domain (x : Λ) (hx : x ∈ K) : x.val ∈ e.baseSet := (nativeBounds x (inside hx)).1
  obtain ⟨η,positiveη,transports⟩ := h.exists_uniform_projection_transport e K compact domain θ positive small
  obtain ⟨δ,positiveδ,insideW⟩ := CompactNearDiagonalContinuity.exists_radius K W compact openW
    inside id continuousOn_id 1 zero_lt_one
  refine ⟨min η δ,lt_min positiveη positiveδ,fun x hx y near => ?_⟩
  have hyW : y ∈ W := (insideW x hx y (near.trans_le (min_le_right _ _))).1
  have boundsX := nativeBounds x (inside hx)
  have boundsY := nativeBounds y hyW
  obtain ⟨hy,R,_actual,commutes,closeR,normR,inverseR⟩ :=
    transports x hx y (near.trans_le (min_le_left _ _))
  let native := ProjectionFiberTransport.map fibers e x.val y.val boundsX.1 hy R
  refine ⟨native,?_,?_,?_,?_⟩
  · exact ProjectionFiberTransport.intertwines fibers e h.projection x.val y.val boundsX.1 hy R commutes
  · calc
      _ ≤ C * ‖R.toContinuousLinearMap‖ * C :=
        ProjectionFiberTransport.norm_le fibers e x.val y.val boundsX.1 hy R C C boundsX.2.1 boundsY.2.2
      _ ≤ C * (1 + θ) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left normR positiveC.le) positiveC.le
      _ = C ^ 2 * (1 + θ) := by ring
  · calc
      _ ≤ C * ‖R.symm.toContinuousLinearMap‖ * C :=
        ProjectionFiberTransport.inverse_norm_le fibers e x.val y.val boundsX.1 hy R C C boundsY.2.1 boundsX.2.2
      _ ≤ C * (1 / (1 - θ)) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left inverseR positiveC.le) positiveC.le
      _ = C ^ 2 / (1 - θ) := by ring

  · have represented : (e.continuousLinearMapAt ℝ y.val).comp
        (native.toContinuousLinearMap.comp (e.symmL ℝ x.val)) = R.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro v
      change e.continuousLinearMapAt ℝ y.val
        (ProjectionFiberTransport.map fibers e x.val y.val boundsX.1 hy R (e.symmL ℝ x.val v)) = R v
      rw [ProjectionFiberTransport.map_apply, e.continuousLinearMapAt_symmL boundsX.1,
        e.continuousLinearMapAt_symmL hy]
    rw [represented]
    exact closeR

end LeanShared.HyperbolicBasicSet
