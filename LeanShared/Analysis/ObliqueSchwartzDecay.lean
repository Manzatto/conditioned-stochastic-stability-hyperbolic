module
public import LeanShared.Geometry.AffineGraphGeometry
public import LeanShared.Analysis.SchwartzKernelBounds
public import LeanShared.Analysis.GraphLeafNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual Schwartz test functions decay uniformly in the transverse
coordinate of a fixed affine graph family, with explicit finite seminorms. -/
public noncomputable section
open Set
open scoped SchwartzMap
namespace LeanShared.ObliqueSchwartzDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem transverse_norm (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (u : U) (v : Uᗮ) :
    ‖v‖ ≤ (1+‖L‖)*‖AffineGraphParameter.point U L v u‖ := by
  let x := AffineGraphParameter.point U L v u
  have pu : U.orthogonalProjectionOnto x=u := AffineGraphParameter.projection_point U L v u
  have pv : Uᗮ.orthogonalProjectionOnto x=L u+v := by
    change Uᗮ.orthogonalProjectionOnto
      (IntrinsicGraphJacobian.graphDifferential U L u+(v:E))=L u+v
    rw [map_add,AffineGraphParameter.normal_projection,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hu : ‖u‖ ≤ ‖x‖ := by
    rw [← pu]; exact U.norm_orthogonalProjectionOnto_apply_le x
  have hv : ‖L u+v‖ ≤ ‖x‖ := by
    rw [← pv]; exact Uᗮ.norm_orthogonalProjectionOnto_apply_le x
  calc
    ‖v‖ = ‖(L u+v)-L u‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖L u+v‖+‖L u‖ := norm_sub_le _ _
    _ ≤ ‖x‖+‖L‖*‖u‖ := add_le_add hv (L.le_opNorm u)
    _ ≤ (1+‖L‖)*‖x‖ := by nlinarith [norm_nonneg L]

@[expose] def seminorm (m : ℕ) : Seminorm ℂ 𝓢(E,ℂ) :=
  (Finset.Iic (m,0)).sup (fun j => SchwartzMap.seminorm ℂ j.1 j.2)

theorem decay (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (m : ℕ)
    (test : 𝓢(E,ℂ)) (u : U) (v : Uᗮ) :
    ‖test (AffineGraphParameter.point U L v u)‖ ≤
      ((1+‖L‖)^m*2^m*seminorm m test)*GraphLeafNorm.radialWeight (m:ℝ) v := by
  let x := AffineGraphParameter.point U L v u
  have base : 1+‖v‖ ≤ (1+‖L‖)*(1+‖x‖) := by
    have bound := transverse_norm U L u v
    change ‖v‖ ≤ (1+‖L‖)*‖x‖ at bound
    nlinarith [norm_nonneg L]
  have polynomial : (1+‖x‖)^m*‖test x‖ ≤ 2^m*seminorm m test := by
    simpa only [seminorm,norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m,0))
        (k := m) (n := 0) le_rfl le_rfl test x
  have weighted : (1+‖v‖)^m*‖test x‖ ≤ (1+‖L‖)^m*2^m*seminorm m test := by
    calc
      _ ≤ ((1+‖L‖)*(1+‖x‖))^m*‖test x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) base m) (norm_nonneg _)
      _ = (1+‖L‖)^m*((1+‖x‖)^m*‖test x‖) := by rw [mul_pow,mul_assoc]
      _ ≤ (1+‖L‖)^m*(2^m*seminorm m test) :=
        mul_le_mul_of_nonneg_left polynomial (by positivity)
      _ = _ := (mul_assoc _ _ _).symm
  change ‖test x‖ ≤ _*(1+‖v‖)^(-(m:ℝ))
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast,← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using weighted
end LeanShared.ObliqueSchwartzDecay
