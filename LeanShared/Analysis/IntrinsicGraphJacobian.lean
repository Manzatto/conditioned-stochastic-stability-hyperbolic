module
public import LeanShared.Analysis.GraphJacobian
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Identify the graph density with the intrinsic rectangular Jacobian of
the ambient parametrization, before constructing any leaf measure. -/
public noncomputable section
open scoped RealInnerProductSpace
namespace LeanShared.IntrinsicGraphJacobian
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

@[expose] def graphDifferential (U : Submodule ℝ E) (D : U →L[ℝ] Uᗮ) : U →L[ℝ] E :=
  U.subtypeL + Uᗮ.subtypeL.comp D

omit [FiniteDimensional ℝ E] in
theorem gram_graph (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U)
    (D : U →L[ℝ] Uᗮ) :
    Matrix.gram ℝ (fun i => graphDifferential U D (b i)) = GraphJacobian.gram b D := by
  ext i j
  have cross₁ : inner ℝ ((b i : U) : E) ((D (b j) : Uᗮ) : E) = 0 :=
    ((U.mem_orthogonal _).mp (D (b j)).property) _ (b i).property
  have cross₂ : inner ℝ ((D (b i) : Uᗮ) : E) ((b j : U) : E) = 0 :=
    real_inner_comm _ _ |>.trans (((U.mem_orthogonal _).mp (D (b i)).property) _ (b j).property)
  simp only [Matrix.gram_apply, graphDifferential, add_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, inner_add_left, inner_add_right,
    cross₁, cross₂, add_zero, zero_add]
  change inner ℝ (b i) (b j) + inner ℝ (D (b i)) (D (b j)) = _
  rw [b.inner_eq_ite]
  rfl

theorem normDet_graph (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U)
    (D : U →L[ℝ] Uᗮ) :
    (graphDifferential U D).toLinearMap.normDet = GraphJacobian.density b D := by
  rw [GraphJacobian.density, ← gram_graph U b D]
  have sq : (Matrix.gram ℝ (fun i => graphDifferential U D (b i))).det =
      (graphDifferential U D).toLinearMap.normDet ^ 2 :=
    (LinearMap.normDet_sq_eq_det_gram (graphDifferential U D).toLinearMap b).symm
  rw [sq, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-- Intrinsic density transforms by the ordinary coordinate Jacobian. -/
theorem coordinate_change (U : Submodule ℝ E) (A : U →ₗ[ℝ] E) (J : U →ₗ[ℝ] U) :
    (A.comp J).normDet = A.normDet * |J.det| := by
  rw [LinearMap.normDet_comp_of_finrank_eq J A rfl, LinearMap.normDet_eq_norm_det,
    Real.norm_eq_abs]
end LeanShared.IntrinsicGraphJacobian
