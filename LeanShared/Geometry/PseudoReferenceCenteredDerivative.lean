module
public import LeanShared.Geometry.PseudoReferenceCoordinateMaps
public import LeanShared.Geometry.CenteredAtlasMisalignedCoordinates
public import LeanShared.Geometry.CenteredTransportDerivativeIdentity
public import LeanShared.Geometry.ProjectionFiberRoundTrip
public import LeanShared.Analysis.MisalignedDerivativeNorm

/-! The actual centered derivative at a nearby reference target differs from
the transported native derivative by the proved inverse transport error.
This is the genuine derivative of the map, not a supplied cocycle identity. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open CenteredManifoldCoordinates

set_option maxHeartbeats 1600000 in
theorem centered_derivative_error
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
    (d : HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (H : M → M) (x y : Λ) (smooth : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val)
    (target : H x.val ∈ (chart d y).source)
    (R : TangentSpace (𝓘(ℝ, E)) (H x.val) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val)
    (θ : ℝ) (small : θ < 1)
    (bound : let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) (d.index y).val
      ‖(e.continuousLinearMapAt ℝ (H x.val)).comp
        (R.symm.toContinuousLinearMap.comp (e.symmL ℝ y.val)) - ContinuousLinearMap.id ℝ E‖ ≤ θ) :
    let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) (d.index y).val
    ‖fderiv ℝ (centered (linear d frame x) (linear d frame y)
        ((chart d x) x.val) ((chart d y) y.val) (chart d y ∘ H ∘ (chart d x).symm)) 0 -
      (frame y).symm.toContinuousLinearMap.comp
        (R.toContinuousLinearMap.comp ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp
          (frame x).toContinuousLinearMap))‖ ≤
      ‖(linear d frame y).symm.toContinuousLinearMap‖ * (θ / (1 - θ)) *
        ‖(e.continuousLinearMapAt ℝ (H x.val)).comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap)‖ := by
  intro e
  let fibers := fun z : M => TangentSpace (𝓘(ℝ, E)) z
  have hx : H x.val ∈ e.baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact target
  have hy : y.val ∈ e.baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact inside d y
  let D := (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap
  let A := (e.continuousLinearMapAt ℝ (H x.val)).comp D
  let C := ProjectionFiberTransport.inverseCoordinates fibers e (H x.val) y.val hx hy R
  have coordinateBound : ‖C.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ ≤ θ := by
    rw [ProjectionFiberTransport.inverseCoordinates_formula]
    exact bound
  have normalization : linear d frame y = (frame y).trans (e.continuousLinearEquivAt ℝ y.val hy) := by
    ext v
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chart d y) y.val))
      ((CompactRiemannianChartBounds.chart_differentiable (chart d y) (chart_mem d y)).mfderiv
        (inside d y) (frame y v)) = e.continuousLinearEquivAt ℝ y.val hy (frame y v)
    rw [Trivialization.coe_continuousLinearEquivAt_eq, TangentChartTrivialization.forward (inside d y)]
    rfl
  have raw := CenteredAtlasCoordinates.hasFDerivAt_misaligned_target H x.val y.val
    (chart d x) (chart d y)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem d x))
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem d y))
    (inside d x) target (inside d y) (frame x) (frame y) smooth
  have derivative : HasFDerivAt
      (centered (linear d frame x) (linear d frame y) ((chart d x) x.val) ((chart d y) y.val)
        (chart d y ∘ H ∘ (chart d x).symm))
      ((linear d frame y).symm.toContinuousLinearMap.comp A) 0 := by
    convert raw using 1
    · rfl
    · change (linear d frame y).symm.toContinuousLinearMap.comp
        ((e.continuousLinearMapAt ℝ (H x.val)).comp D) = _
      rw [TangentChartTrivialization.forward target]
      ext v
      rfl
  have physical := CenteredTransportDerivativeIdentity.physical_transport fibers e (H x.val) y.val
    hx hy (frame y) C D
  rw [ProjectionFiberTransport.round_trip, ← normalization] at physical
  rw [derivative.fderiv, ← physical]
  exact MisalignedDerivativeNorm.inverse_transport_error C (linear d frame y) A small coordinateBound

end LeanShared.PseudoReferenceCoordinateMaps
