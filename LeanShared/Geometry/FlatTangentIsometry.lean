module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Tactic.Linarith

/-! Canonical Euclidean tangent normalization is an actual isometry for
the genuine flat Riemannian metric. Composing an arbitrary finite-source
map with an isometry preserves its Gram-volume determinant. -/
public noncomputable section
namespace LeanShared.FlatTangentIsometry
open Bundle
open scoped Manifold
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[expose] def equivalence (x : F) : TangentSpace (𝓘(ℝ,F)) x ≃ₗᵢ[ℝ] F :=
  { (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toLinearEquiv with
    norm_map' := fun v => (norm_tangentSpace_vectorSpace (v := v)).symm }

end LeanShared.FlatTangentIsometry

namespace LeanShared.NormDetIsometry
variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem comp (A : U →ₗ[ℝ] V) (J : V →ₗᵢ[ℝ] W) : (J.toLinearMap.comp A).normDet = A.normDet := by
  let b := stdOrthonormalBasis ℝ U
  have gram : Matrix.gram ℝ (fun i => (J.toLinearMap.comp A) (b i)) =
      Matrix.gram ℝ (fun i => A (b i)) := by
    ext i j
    simp only [Matrix.gram_apply, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
    exact J.inner_map_map _ _
  have first := (J.toLinearMap.comp A).normDet_sq_eq_det_gram b
  have other := A.normDet_sq_eq_det_gram b
  change (J.toLinearMap.comp A).normDet ^ 2 = (Matrix.gram ℝ (fun i => (J.toLinearMap.comp A) (b i))).det at first
  change A.normDet ^ 2 = (Matrix.gram ℝ (fun i => A (b i))).det at other
  have squared : (J.toLinearMap.comp A).normDet ^ 2 = A.normDet ^ 2 :=
    first.trans ((congrArg Matrix.det gram).trans other.symm)
  nlinarith [LinearMap.normDet_nonneg (J.toLinearMap.comp A), LinearMap.normDet_nonneg A]

end LeanShared.NormDetIsometry
