module
public import LeanShared.Analysis.NilpotentResolvent
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! A contour around zero for a genuinely nilpotent operator is the identity. -/
public noncomputable section
open Set Metric
open scoped BigOperators
namespace LeanShared.NilpotentResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem scalar_circle (k : ℕ) (R : ℝ) (hR : 0 < R) :
    (∮ z in C(0,R), (z⁻¹)^(k+1)) = if k=0 then (2*Real.pi*Complex.I : ℂ) else 0 := by
  by_cases hk : k=0
  · subst k
    rw [ite_eq_left rfl]
    simpa only [zero_add, pow_one, sub_zero] using
      (circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hR) :
        (∮ z in C(0,R), (z-0)⁻¹) = (2*Real.pi*Complex.I : ℂ))
  · rw [ite_eq_right hk]
    have scalar := circleIntegral.integral_sub_zpow_of_ne
      (n := -((k+1 : ℕ) : ℤ)) (by omega) (0 : ℂ) 0 R
    simpa only [sub_zero, zpow_neg, zpow_natCast, inv_pow] using scalar

theorem circle_integral_eq_one (N : A) (n : ℕ) (nilpotent : N^n=0)
    (R : ℝ) (hR : 0 < R) : RieszContourIdempotent.projector N 0 R = 1 := by
  classical
  by_cases zero : n=0
  · subst n
    have oneZero : (1 : A)=0 := by simpa only [pow_zero] using nilpotent
    have : Subsingleton A := subsingleton_of_zero_eq_one oneZero.symm
    exact Subsingleton.elim _ _
  have circleEq : (∮ z in C(0,R), resolvent N z) =
      ∮ z in C(0,R), laurent N n z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    apply formula N n nilpotent z
    intro zzero
    exact hR.ne' (by simpa only [zzero, mem_sphere, dist_self] using hz.symm)
  have intTerm (k : ℕ) : CircleIntegrable (fun z : ℂ => (z⁻¹)^(k+1) • N^k) 0 R := by
    have nonzero : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
      intro z hz he
      subst z
      exact hR.ne' (by simpa only [mem_sphere, dist_self] using hz.symm)
    exact (((continuousOn_id.inv₀ nonzero).pow (k+1)).smul continuousOn_const).circleIntegrable hR.le
  have integral : (∮ z in C(0,R), laurent N n z) = (2*Real.pi*Complex.I : ℂ) • (1 : A) := by
    change (∮ z in C(0,R), ∑ k ∈ Finset.range n, (z⁻¹)^(k+1) • N^k) = _
    rw [circleIntegral.integral_fun_sum (fun k _ => intTerm k)]
    simp_rw [circleIntegral.integral_smul_const, scalar_circle _ R hR]
    rw [Finset.sum_eq_single 0]
    · simp only [ite_true, pow_zero]
    · intro k _ hk
      simp only [ite_eq_right hk, zero_smul]
    · intro absent
      exact False.elim (absent (Finset.mem_range.mpr (Nat.pos_of_ne_zero zero)))
  change (2*Real.pi*Complex.I : ℂ)⁻¹ • (∮ z in C(0,R), resolvent N z) = 1
  rw [circleEq,integral,inv_smul_smul₀ Complex.two_pi_I_ne_zero]
end LeanShared.NilpotentResolvent
