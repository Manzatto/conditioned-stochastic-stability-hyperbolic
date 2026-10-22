module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Actual resolvent formula for a diagonal pair of bounded operators. -/

public section
open ContinuousLinearMap
namespace LeanShared.BlockResolvent
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual inverse of a diagonal shifted operator is the pair of actual
inverses of its blocks. No spectral splitting theorem is assumed. -/
theorem formula (A : E →L[ℂ] E) (B : F →L[ℂ] F) (z : ℂ)
    (hA : z ∈ resolventSet ℂ A) (hB : z ∈ resolventSet ℂ B) :
    z ∈ resolventSet ℂ (A.prodMap B) ∧
      resolvent (A.prodMap B) z = (resolvent A z).prodMap (resolvent B z) := by
  let Q := (resolvent A z).prodMap (resolvent B z)
  let S := z • (1 : E × F →L[ℂ] E × F) - A.prodMap B
  have leftA : resolvent A z * (z • 1 - A) = 1 := Ring.inverse_mul_cancel _ hA
  have rightA : (z • 1 - A) * resolvent A z = 1 := Ring.mul_inverse_cancel _ hA
  have leftB : resolvent B z * (z • 1 - B) = 1 := Ring.inverse_mul_cancel _ hB
  have rightB : (z • 1 - B) * resolvent B z = 1 := Ring.mul_inverse_cancel _ hB
  have left : Q * S = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · change (resolvent A z) (z • x.1 - A x.1) = x.1
      have hh := congrArg (fun P : E →L[ℂ] E => P x.1) leftA
      simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh
    · change (resolvent B z) (z • x.2 - B x.2) = x.2
      have hh := congrArg (fun P : F →L[ℂ] F => P x.2) leftB
      simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh
  have right : S * Q = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · change z • (resolvent A z) x.1 - A ((resolvent A z) x.1) = x.1
      have hh := congrArg (fun P : E →L[ℂ] E => P x.1) rightA
      simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh
    · change z • (resolvent B z) x.2 - B ((resolvent B z) x.2) = x.2
      have hh := congrArg (fun P : F →L[ℂ] F => P x.2) rightB
      simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh
  have hunit : IsUnit S := ⟨⟨S, Q, right, left⟩, rfl⟩
  refine ⟨hunit, ?_⟩
  change Ring.inverse S = Q
  calc
    Ring.inverse S = Ring.inverse S * 1 := (mul_one _).symm
    _ = Ring.inverse S * (S * Q) := by rw [right]
    _ = (Ring.inverse S * S) * Q := (mul_assoc _ _ _).symm
    _ = Q := by rw [Ring.inverse_mul_cancel S hunit, one_mul]

end LeanShared.BlockResolvent
