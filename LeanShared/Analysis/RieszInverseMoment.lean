module
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Module

/-! Inverse contour moments construct inverse powers on the actual Riesz range.
The contour excludes zero; no inverse on the full ambient space is assumed. -/
public noncomputable section
open Set Metric
namespace LeanShared.RieszInverseMoment
open RieszContourIdempotent ContourProjectorContinuity
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def moment (T : A) (n : ℕ) (c : ℂ) (R : ℝ) : A :=
  contour (fun z : ℂ => (z^n)⁻¹ • resolvent T z) c R

omit [CompleteSpace A] in
theorem zero (T : A) (c : ℂ) (R : ℝ) : moment T 0 c R=projector T c R := by
  simp only [moment,pow_zero,inv_one,one_smul,projector]

theorem scalar_integral_zero (n : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (excludes : (0 : ℂ) ∉ closedBall c R) :
    (∮ z in C(c,R), (z^n)⁻¹)=0 := by
  have nonzero : ∀ z ∈ closedBall c R, z ≠ (0 : ℂ) := by
    intro z hz he
    subst z
    exact excludes hz
  have differentiable : ∀ z ∈ closedBall c R,
      DifferentiableAt ℂ (fun z : ℂ => (z^n)⁻¹) z := by
    intro z hz
    exact (differentiableAt_id.pow n).inv (pow_ne_zero n (nonzero z hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    (fun z hz => (differentiable z hz).continuousAt.continuousWithinAt)
    (fun z hz => differentiable z (ball_subset_closedBall hz.1))

theorem recurrence (T : A) (n : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (excludes : (0 : ℂ) ∉ closedBall c R) (res : sphere c R ⊆ resolventSet ℂ T) :
    T*moment T (n+1) c R=moment T n c R ∧
      moment T (n+1) c R*T=moment T n c R := by
  have nonzero : ∀ z ∈ sphere c R, z ≠ (0 : ℂ) := by
    intro z hz he
    subst z
    exact excludes (sphere_subset_closedBall hz)
  have scalarContinuous (m : ℕ) : ContinuousOn (fun z : ℂ => (z^m)⁻¹) (sphere c R) :=
    (continuousOn_id.pow m).inv₀ (fun z hz => pow_ne_zero m (nonzero z hz))
  have resContinuous : ContinuousOn (resolvent T) (sphere c R) := fun z hz =>
    (spectrum.hasDerivAt_resolvent_const_left (res hz)).continuousAt.continuousWithinAt
  have integrable (m : ℕ) : CircleIntegrable (fun z : ℂ => (z^m)⁻¹ • resolvent T z) c R :=
    ((scalarContinuous m).smul resContinuous).circleIntegrable hR
  have constantInt : CircleIntegrable (fun z : ℂ => (z^(n+1))⁻¹ • (1 : A)) c R :=
    ((scalarContinuous (n+1)).smul continuousOn_const).circleIntegrable hR
  have scalar (z : ℂ) (hz : z ∈ sphere c R) : (z^(n+1))⁻¹*z=(z^n)⁻¹ := by
    rw [pow_succ,mul_inv_rev,mul_assoc,mul_comm (z^n)⁻¹ z,← mul_assoc,
      inv_mul_cancel₀ (nonzero z hz),one_mul]
  have pointLeft (z : ℂ) (hz : z ∈ sphere c R) :
      T*((z^(n+1))⁻¹ • resolvent T z)=
        (z^n)⁻¹ • resolvent T z-(z^(n+1))⁻¹ • (1 : A) := by
    have relation : T*resolvent T z=z•resolvent T z-1 := by
      have hh : (algebraMap ℂ A z-T)*resolvent T z=1 := Ring.mul_inverse_cancel _ (res hz)
      simp only [sub_mul,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] at hh
      apply eq_sub_iff_add_eq.mpr
      rw [add_comm]
      exact (sub_eq_iff_eq_add.mp hh).symm
    rw [mul_smul_comm,relation,smul_sub,smul_smul,scalar z hz]
  have pointRight (z : ℂ) (hz : z ∈ sphere c R) :
      ((z^(n+1))⁻¹ • resolvent T z)*T=
        (z^n)⁻¹ • resolvent T z-(z^(n+1))⁻¹ • (1 : A) := by
    have relation : resolvent T z*T=z•resolvent T z-1 := by
      have hh : resolvent T z*(algebraMap ℂ A z-T)=1 := Ring.inverse_mul_cancel _ (res hz)
      simp only [mul_sub,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one] at hh
      apply eq_sub_iff_add_eq.mpr
      rw [add_comm]
      exact (sub_eq_iff_eq_add.mp hh).symm
    rw [smul_mul_assoc,relation,smul_sub,smul_smul,scalar z hz]
  have integral : (2*Real.pi*Complex.I : ℂ)⁻¹ •
      (∮ z in C(c,R), (z^n)⁻¹ • resolvent T z-(z^(n+1))⁻¹ • (1 : A))=
        moment T n c R := by
    rw [circleIntegral.integral_sub (integrable n) constantInt,
      circleIntegral.integral_smul_const,scalar_integral_zero (n+1) c R hR excludes,
      zero_smul,sub_zero]
    rfl
  constructor
  · unfold moment contour
    have mapped : T*(∮ z in C(c,R), (z^(n+1))⁻¹ • resolvent T z)=
        ∮ z in C(c,R), T*((z^(n+1))⁻¹ • resolvent T z) :=
      map_circleIntegral (ContinuousLinearMap.mul ℂ A T) _ c R (integrable (n+1))
    rw [mul_smul_comm,mapped]
    rw [circleIntegral.integral_congr hR pointLeft]
    exact integral
  · unfold moment contour
    have mapped : (∮ z in C(c,R), (z^(n+1))⁻¹ • resolvent T z)*T=
        ∮ z in C(c,R), ((z^(n+1))⁻¹ • resolvent T z)*T :=
      map_circleIntegral ((ContinuousLinearMap.mul ℂ A).flip T) _ c R (integrable (n+1))
    rw [smul_mul_assoc,mapped]
    rw [circleIntegral.integral_congr hR pointRight]
    exact integral

theorem powers (T : A) (n : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (excludes : (0 : ℂ) ∉ closedBall c R) (res : sphere c R ⊆ resolventSet ℂ T) :
    T^n*moment T n c R=projector T c R ∧
      moment T n c R*T^n=projector T c R := by
  induction n with
  | zero => simp only [pow_zero,one_mul,mul_one,zero,and_self]
  | succ n ih =>
    have step := recurrence T n c R hR excludes res
    constructor
    · rw [pow_succ,mul_assoc,step.1]
      exact ih.1
    · rw [pow_succ',← mul_assoc,step.2]
      exact ih.2
end LeanShared.RieszInverseMoment
