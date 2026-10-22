module
public import LeanShared.Analysis.AffineGraphParameter
public import LeanShared.Geometry.AffineImmersionChart
public import LeanShared.Geometry.EmbeddedSubmanifoldVolume

/-! A full affine graph is an actual embedded manifold and has its actual
operator-norm secant slope, including translated graphs. -/
public noncomputable section
open Set
namespace LeanShared.AffineGraphParameter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem embedded (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) :
    EmbeddedSubmanifoldVolume.Embedded U (carrier U L v) := by
  exact AffineImmersionChart.exists_chart
    (IntrinsicGraphJacobian.graphDifferential U L) U.orthogonalProjectionOnto
    (IntrinsicGraphJacobian.projection_graphDifferential U L) (v:E)

theorem normal_projection (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (u : U) :
    Uᗮ.orthogonalProjectionOnto (IntrinsicGraphJacobian.graphDifferential U L u)=L u := by
  change Uᗮ.orthogonalProjectionOnto ((u:E)+(L u:E))=L u
  rw [map_add,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have zero : Uᗮ.orthogonalProjectionOnto (u:E)=0 :=
    (Uᗮ.orthogonalProjectionOnto_eq_zero_iff).mpr
      (by rw [Submodule.orthogonal_orthogonal]; exact u.property)
  rw [zero,zero_add]

theorem slope (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ) :
    ∀ x ∈ carrier U L v, ∀ y ∈ carrier U L v,
      ‖Uᗮ.starProjection (x-y)‖ ≤ ‖L‖*‖U.starProjection (x-y)‖ := by
  rintro x ⟨u,rfl⟩ y ⟨w,rfl⟩
  have difference : point U L v u-point U L v w=
      IntrinsicGraphJacobian.graphDifferential U L (u-w) := by
    rw [map_sub]
    exact add_sub_add_right_eq_sub _ _ _
  rw [difference]
  change ‖Uᗮ.orthogonalProjectionOnto (IntrinsicGraphJacobian.graphDifferential U L (u-w))‖ ≤
    ‖L‖*‖U.orthogonalProjectionOnto (IntrinsicGraphJacobian.graphDifferential U L (u-w))‖
  rw [normal_projection,IntrinsicGraphJacobian.projection_graphDifferential]
  exact L.le_opNorm _
end LeanShared.AffineGraphParameter
