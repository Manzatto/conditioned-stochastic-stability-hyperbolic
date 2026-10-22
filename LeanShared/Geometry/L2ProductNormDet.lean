module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Genuine norm determinants multiply under Hilbert direct products,
including zero-dimensional factors and arbitrary factor metrics. -/
public noncomputable section
open Module
namespace LeanShared.L2ProductNormDet
variable {U U' V V' : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup U'] [InnerProductSpace ℝ U'] [FiniteDimensional ℝ U']
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']

@[expose] def productEquiv (A : U ≃ₗ[ℝ] V) (B : U' ≃ₗ[ℝ] V') :
    WithLp 2 (U × U') ≃ₗ[ℝ] WithLp 2 (V × V') :=
  (WithLp.linearEquiv 2 ℝ (U × U')).trans
    ((A.prodCongr B).trans (WithLp.linearEquiv 2 ℝ (V × V')).symm)

theorem normDet_product (A : U ≃ₗ[ℝ] V) (B : U' ≃ₗ[ℝ] V') :
    (productEquiv A B).toLinearMap.normDet=A.toLinearMap.normDet*B.toLinearMap.normDet := by
  classical
  let bu := stdOrthonormalBasis ℝ U
  let bu' := stdOrthonormalBasis ℝ U'
  let bv := (stdOrthonormalBasis ℝ V).reindex (finCongr A.finrank_eq.symm)
  let bv' := (stdOrthonormalBasis ℝ V').reindex (finCongr B.finrank_eq.symm)
  have matrix : (productEquiv A B).toLinearMap.toMatrix (bu.prod bu').toBasis (bv.prod bv').toBasis =
      Matrix.fromBlocks (A.toLinearMap.toMatrix bu.toBasis bv.toBasis) 0 0
        (B.toLinearMap.toMatrix bu'.toBasis bv'.toBasis) := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply,OrthonormalBasis.prod,productEquiv]
  rw [LinearMap.normDet_eq_norm_det_toMatrix _ (bu.prod bu') (bv.prod bv'),matrix,
    Matrix.det_fromBlocks_zero₂₁,norm_mul,
    ←LinearMap.normDet_eq_norm_det_toMatrix A.toLinearMap bu bv,
    ←LinearMap.normDet_eq_norm_det_toMatrix B.toLinearMap bu' bv']

end LeanShared.L2ProductNormDet
