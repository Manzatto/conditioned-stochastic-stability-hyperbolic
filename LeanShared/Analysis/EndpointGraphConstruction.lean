module
public import LeanShared.Geometry.BoundedProjectionGraph

/-! Construct endpoint-image and stable-preimage graphs from actual
subspaces and their orthogonal cone-slope inequalities. -/
public noncomputable section
namespace LeanShared.EndpointGraphConstruction
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_image_graph (U : Submodule ℝ E) (B : U →L[ℝ] E)
    (dimension : Module.finrank ℝ B.toLinearMap.range = Module.finrank ℝ U)
    {L : ℝ} (nonnegative : 0 ≤ L)
    (slope : ∀ w : B.toLinearMap.range, ‖Uᗮ.orthogonalProjectionOnto (w : E)‖ ≤
      L * ‖U.orthogonalProjectionOnto (w : E)‖) :
    ∃ H : U →L[ℝ] Uᗮ, ‖H‖ ≤ L ∧ B =
      (IntrinsicGraphJacobian.graphDifferential U H).comp (U.orthogonalProjectionOnto.comp B) := by
  obtain ⟨H, bound, range⟩ := BoundedProjectionGraph.exists_graph U B.toLinearMap.range
    dimension nonnegative slope
  refine ⟨H, bound, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  have member : B u ∈ (IntrinsicGraphJacobian.graphDifferential U H).toLinearMap.range := by
    rw [range]
    exact ⟨u, rfl⟩
  obtain ⟨v, equal⟩ := member
  have projection := congrArg U.orthogonalProjectionOnto equal
  change U.orthogonalProjectionOnto (IntrinsicGraphJacobian.graphDifferential U H v) =
    U.orthogonalProjectionOnto (B u) at projection
  rw [IntrinsicGraphJacobian.projection_graphDifferential] at projection
  change B u = IntrinsicGraphJacobian.graphDifferential U H
    (U.orthogonalProjectionOnto (B u))
  exact equal.symm.trans (congrArg (IntrinsicGraphJacobian.graphDifferential U H) projection)

theorem exists_preimage_graph (U S : Submodule ℝ E)
    (dimension : Module.finrank ℝ S = Module.finrank ℝ Uᗮ)
    {L : ℝ} (nonnegative : 0 ≤ L)
    (slope : ∀ w : S, ‖U.orthogonalProjectionOnto (w : E)‖ ≤
      L * ‖Uᗮ.orthogonalProjectionOnto (w : E)‖) :
    ∃ J : Uᗮ →L[ℝ] U, ‖J‖ ≤ L ∧
      ∀ v : Uᗮ, (J v : E) + (v : E) ∈ S := by
  have slope' : ∀ w : S, ‖Uᗮᗮ.orthogonalProjectionOnto (w : E)‖ ≤
      L * ‖Uᗮ.orthogonalProjectionOnto (w : E)‖ := by
    intro w
    change ‖Uᗮᗮ.starProjection (w : E)‖ ≤ L * ‖Uᗮ.starProjection (w : E)‖
    have double : Uᗮᗮ.starProjection = U.starProjection := by
      rw [Submodule.starProjection_orthogonal Uᗮ, Submodule.starProjection_orthogonal U]
      abel
    rw [double]
    exact slope w
  obtain ⟨D, bound, range⟩ := BoundedProjectionGraph.exists_graph Uᗮ S
    dimension nonnegative slope'
  let e : Uᗮᗮ ≃ₗᵢ[ℝ] U := LinearIsometryEquiv.ofEq Uᗮᗮ U (Submodule.orthogonal_orthogonal U)
  let J : Uᗮ →L[ℝ] U := e.toContinuousLinearEquiv.toContinuousLinearMap.comp D
  have value (v : Uᗮ) : (J v : E) = (D v : E) := rfl
  refine ⟨J, ContinuousLinearMap.opNorm_le_bound _ nonnegative ?_, ?_⟩
  · intro v
    calc
      ‖J v‖ = ‖D v‖ := e.norm_map _
      _ ≤ ‖D‖ * ‖v‖ := D.le_opNorm v
      _ ≤ L * ‖v‖ := mul_le_mul_of_nonneg_right bound (norm_nonneg _)
  · intro v
    have member : IntrinsicGraphJacobian.graphDifferential Uᗮ D v ∈ S := by
      rw [← range]
      exact ⟨v, rfl⟩
    change (v : E) + (D v : E) ∈ S at member
    rw [value, add_comm]
    exact member
end LeanShared.EndpointGraphConstruction
