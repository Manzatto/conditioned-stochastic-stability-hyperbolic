module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Analysis.IntertwinedProjectionSubspaces

/-! Actual tangent-fiber transport restricts to the actual stable and unstable
bundles, inheriting both native Riemannian norm bounds. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_restricted_transport
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (x y : Λ) (R : TangentSpace (𝓘(ℝ, E)) x.val ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val)
    (commutes : ∀ v, h.projection y.val (R v) = R (h.projection x.val v)) :
    ∃ S : h.stable x.val ≃L[ℝ] h.stable y.val,
    ∃ U : h.unstable x.val ≃L[ℝ] h.unstable y.val,
      ‖S.toContinuousLinearMap‖ ≤ ‖R.toContinuousLinearMap‖ ∧
      ‖S.symm.toContinuousLinearMap‖ ≤ ‖R.symm.toContinuousLinearMap‖ ∧
      ‖U.toContinuousLinearMap‖ ≤ ‖R.toContinuousLinearMap‖ ∧
      ‖U.symm.toContinuousLinearMap‖ ≤ ‖R.symm.toContinuousLinearMap‖ ∧
      (∀ v, (S v).val = R v.val) ∧ (∀ v, (U v).val = R v.val) := by
  have stable : (h.stable x.val).map R.toLinearMap = h.stable y.val := by
    rw [← h.projection_range x.val x.property, ← h.projection_range y.val y.property]
    exact IntertwinedProjectionSubspaces.range_map _ _ R commutes
  have unstable : (h.unstable x.val).map R.toLinearMap = h.unstable y.val := by
    rw [← h.projection_kernel x.val x.property, ← h.projection_kernel y.val y.property]
    exact IntertwinedProjectionSubspaces.kernel_map _ _ R commutes
  refine ⟨R.ofSubmodules _ _ stable,R.ofSubmodules _ _ unstable,
    IntertwinedProjectionSubspaces.restriction_norm_le R _ _ stable,
    IntertwinedProjectionSubspaces.restriction_inverse_norm_le R _ _ stable,
    IntertwinedProjectionSubspaces.restriction_norm_le R _ _ unstable,
    IntertwinedProjectionSubspaces.restriction_inverse_norm_le R _ _ unstable,?_,?_⟩
  · exact fun v => ContinuousLinearEquiv.ofSubmodules_apply R stable v
  · exact fun v => ContinuousLinearEquiv.ofSubmodules_apply R unstable v

end LeanShared.HyperbolicBasicSet
