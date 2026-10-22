module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact resolvent formula for removing an invariant rank-one spectral
projection. This is purely algebraic and applies to Banach operator algebras
without normality or self-adjointness assumptions. -/

public section

namespace LeanShared.RankOneResolvent

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The resolvent is the complementary resolvent plus an explicit simple-pole
term. Both invertibility and the formula are proved by two-sided multiplication. -/
theorem formula (a p : A) (μ z : 𝕜) (hp : p * p = p)
    (hap : a * p = μ • p) (hpa : p * a = μ • p)
    (hz : z ≠ 0) (hzμ : z ≠ μ)
    (hcomplement : z ∈ resolventSet 𝕜 (a - μ • p)) :
    z ∈ resolventSet 𝕜 a ∧
      resolvent a z = resolvent (a - μ • p) z +
        ((z - μ)⁻¹ - z⁻¹) • p := by
  let b := a - μ • p
  let U := resolvent b z
  let s := z • (1 : A) - b
  have hunit : IsUnit s := by
    simpa only [s, b, spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] using hcomplement
  have hLU : s * U = 1 := by
    simpa only [s, U, resolvent, Algebra.algebraMap_eq_smul_one] using
      Ring.mul_inverse_cancel s hunit
  have hUL : U * s = 1 := by
    simpa only [s, U, resolvent, Algebra.algebraMap_eq_smul_one] using
      Ring.inverse_mul_cancel s hunit
  have hbp : b * p = 0 := by simp only [b, sub_mul, smul_mul_assoc, hp, hap, sub_self]
  have hpb : p * b = 0 := by simp only [b, mul_sub, mul_smul_comm, hp, hpa, sub_self]
  have hsp : s * p = z • p := by simp only [s, sub_mul, smul_mul_assoc, one_mul, hbp, sub_zero]
  have hps : p * s = z • p := by simp only [s, mul_sub, mul_smul_comm, mul_one, hpb, sub_zero]
  have hUp : U * p = z⁻¹ • p := by
    have hh : s * (z⁻¹ • p) = p := by
      rw [mul_smul_comm, hsp, smul_smul, inv_mul_cancel₀ hz, one_smul]
    have hh' := congrArg (fun x : A => U * x) hh
    rw [← mul_assoc, hUL, one_mul] at hh'
    exact hh'.symm
  have hpU : p * U = z⁻¹ • p := by
    have hh : (z⁻¹ • p) * s = p := by
      rw [smul_mul_assoc, hps, smul_smul, inv_mul_cancel₀ hz, one_smul]
    have hh' := congrArg (fun x : A => x * U) hh
    rw [mul_assoc, hLU, mul_one] at hh'
    exact hh'.symm
  have hshift : z • (1 : A) - a = s - μ • p := by dsimp [s, b]; module
  have hleftU : (z • (1 : A) - a) * U = 1 - (μ * z⁻¹) • p := by
    rw [hshift, sub_mul, hLU, smul_mul_assoc, hpU, smul_smul]
  have hrightU : U * (z • (1 : A) - a) = 1 - (μ * z⁻¹) • p := by
    rw [hshift, mul_sub, hUL, mul_smul_comm, hUp, smul_smul]
  have hleftp : (z • (1 : A) - a) * p = (z - μ) • p := by
    rw [sub_mul, smul_mul_assoc, one_mul, hap, sub_smul]
  have hrightp : p * (z • (1 : A) - a) = (z - μ) • p := by
    rw [mul_sub, mul_smul_comm, mul_one, hpa, sub_smul]
  let c := (z - μ)⁻¹ - z⁻¹
  have hc : c * (z - μ) = μ * z⁻¹ := by
    dsimp [c]
    field_simp [hz, sub_ne_zero.mpr hzμ]
    ring
  let B := U + c • p
  have hleft : (z • (1 : A) - a) * B = 1 := by
    dsimp only [B]
    rw [mul_add, hleftU, mul_smul_comm, hleftp, smul_smul, hc]
    abel
  have hright : B * (z • (1 : A) - a) = 1 := by
    dsimp only [B]
    rw [add_mul, hrightU, smul_mul_assoc, hrightp, smul_smul, hc]
    abel
  have hres : z ∈ resolventSet 𝕜 a :=
    spectrum.mem_resolventSet_of_left_right_inverse
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hleft)
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hright)
  refine ⟨hres, ?_⟩
  change Ring.inverse (algebraMap 𝕜 A z - a) = B
  exact left_inv_eq_right_inv (Ring.inverse_mul_cancel _ hres)
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hleft)

end LeanShared.RankOneResolvent
