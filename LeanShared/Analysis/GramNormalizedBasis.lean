module
public import LeanShared.Analysis.MatrixGramNormalizer
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A genuine invertible frame has an explicitly normalized orthonormal
basis, using its actual native Gram matrix. -/
public noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace LeanShared.GramNormalizedBasis
variable {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

@[expose] def gram (A : F ≃L[ℝ] V) : Matrix (Fin (Module.finrank ℝ F)) (Fin (Module.finrank ℝ F)) ℝ :=
  Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ F i))

omit [FiniteDimensional ℝ V] in
theorem positive (A : F ≃L[ℝ] V) : (gram A).PosDef :=
  Matrix.posDef_gram_of_linearIndependent
    ((stdOrthonormalBasis ℝ F).toBasis.linearIndependent.map' A.toLinearMap
      (LinearMap.ker_eq_bot.mpr A.injective))

@[expose] def vectors (A : F ≃L[ℝ] V) (i : Fin (Module.finrank ℝ F)) : V :=
  ∑ j, MatrixGramNormalizer.normalize (gram A) j i • A (stdOrthonormalBasis ℝ F j)

omit [FiniteDimensional ℝ V] in
theorem gram_vectors (A : F ≃L[ℝ] V) : Matrix.gram ℝ (vectors A) = 1 := by
  calc
    _ = star (MatrixGramNormalizer.normalize (gram A))*gram A*
        MatrixGramNormalizer.normalize (gram A) := by
      ext i j
      simp only [Matrix.gram_apply, vectors, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right, star_trivial, Matrix.mul_apply, Matrix.star_apply,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      dsimp [gram, Matrix.gram]
      simp only [starRingEnd_apply, star_trivial]
      ring
    _ = 1 := MatrixGramNormalizer.identity (positive A)

omit [FiniteDimensional ℝ V] in
theorem orthonormal (A : F ≃L[ℝ] V) : Orthonormal ℝ (vectors A) :=
  Matrix.gram_eq_one_iff_orthonormal.mp (gram_vectors A)

@[expose] def basis (A : F ≃L[ℝ] V) : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ V :=
  OrthonormalBasis.mk (orthonormal A)
    ((orthonormal A).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa only [Fintype.card_fin] using A.toLinearEquiv.finrank_eq)).ge

theorem basis_apply (A : F ≃L[ℝ] V) (i : Fin (Module.finrank ℝ F)) :
    basis A i = vectors A i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

end LeanShared.GramNormalizedBasis
