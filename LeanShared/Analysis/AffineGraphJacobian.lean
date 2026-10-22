module
public import LeanShared.Analysis.IntrinsicGraphJacobian
public import LeanShared.Analysis.ConeGraphGeometry
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Actual affine graphs have a constant strictly positive intrinsic area
density. Positivity follows from injectivity of the actual graph derivative. -/
public noncomputable section
namespace LeanShared.IntrinsicGraphJacobian
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

theorem graphDifferential_injective (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ) :
    Function.Injective (graphDifferential U D) :=
  ConeGraphGeometry.graphPoint_injective U D

theorem density_positive (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U)
    (D : U →L[ℝ] Uᗮ) : 0 < GraphJacobian.density b D := by
  rw [← normDet_graph U b D]
  have nonzero : (graphDifferential U D).toLinearMap.normDet ≠ 0 :=
    ((LinearMap.normDet_ne_zero_tfae (graphDifferential U D).toLinearMap).out 1 5).mpr
      (graphDifferential_injective U D)
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) nonzero.symm

theorem projection_graphDifferential (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ) (u : U) :
    U.orthogonalProjectionOnto (graphDifferential U D u)=u := by
  change U.orthogonalProjectionOnto ((u:E)+(D u:E))=u
  rw [map_add,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have zero : U.orthogonalProjectionOnto (D u:E)=0 :=
    (U.orthogonalProjectionOnto_eq_zero_iff).mpr (D u).property
  rw [zero,add_zero]
end LeanShared.IntrinsicGraphJacobian
