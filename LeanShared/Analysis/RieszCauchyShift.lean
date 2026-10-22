module
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Module

/-! The genuine resolvent Cauchy transform solves the complementary shift
on the interior of the contour, whether or not that point is spectral. -/
public noncomputable section
open Set Metric
namespace LeanShared.RieszCauchyShift
open RieszContourIdempotent ContourProjectorContinuity
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem identities (T : A) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (res : sphere c R ⊆ resolventSet ℂ T) (w : ℂ) (hw : w ∈ ball c R) :
    (algebraMap ℂ A w-T)*cauchyTransform T c R w=1-projector T c R ∧
      cauchyTransform T c R w*(algebraMap ℂ A w-T)=1-projector T c R := by
  let s := algebraMap ℂ A w-T
  let G := fun z : ℂ => (z-w)⁻¹ • resolvent T z
  have nz : ∀ z ∈ sphere c R, z-w ≠ 0 := by
    intro z hz he
    have eq := sub_eq_zero.mp he
    subst z
    exact (ne_of_lt hw) hz
  have invContinuous : ContinuousOn (fun z : ℂ => (z-w)⁻¹) (sphere c R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ nz
  have resContinuous : ContinuousOn (resolvent T) (sphere c R) := fun z hz =>
    (spectrum.hasDerivAt_resolvent_const_left (res hz)).continuousAt.continuousWithinAt
  have integrable : CircleIntegrable G c R := (invContinuous.smul resContinuous).circleIntegrable hR
  have scalarInt : CircleIntegrable (fun z : ℂ => (z-w)⁻¹ • (1 : A)) c R :=
    (invContinuous.smul continuousOn_const).circleIntegrable hR
  have resInt : CircleIntegrable (resolvent T) c R := resContinuous.circleIntegrable hR
  have leftPoint (z : ℂ) (hz : z ∈ sphere c R) :
      s*(G z)=(z-w)⁻¹ • (1 : A)-resolvent T z := by
    have shift : s=(algebraMap ℂ A z-T)-(z-w)•1 := by
      dsimp only [s]
      simp only [Algebra.algebraMap_eq_smul_one,sub_smul]
      module
    have relation : s*resolvent T z=1-(z-w)•resolvent T z := by
      have inverse : (algebraMap ℂ A z-T)*resolvent T z=1 := Ring.mul_inverse_cancel _ (res hz)
      rw [shift,sub_mul,inverse,smul_mul_assoc,one_mul]
    dsimp only [G]
    rw [mul_smul_comm,relation,smul_sub,smul_smul,inv_mul_cancel₀ (nz z hz),one_smul]
  have rightPoint (z : ℂ) (hz : z ∈ sphere c R) :
      G z*s=(z-w)⁻¹ • (1 : A)-resolvent T z := by
    have shift : s=(algebraMap ℂ A z-T)-(z-w)•1 := by
      dsimp only [s]
      simp only [Algebra.algebraMap_eq_smul_one,sub_smul]
      module
    have relation : resolvent T z*s=1-(z-w)•resolvent T z := by
      have inverse : resolvent T z*(algebraMap ℂ A z-T)=1 := Ring.inverse_mul_cancel _ (res hz)
      rw [shift,mul_sub,inverse,mul_smul_comm,mul_one]
    dsimp only [G]
    rw [smul_mul_assoc,relation,smul_sub,smul_smul,inv_mul_cancel₀ (nz z hz),one_smul]
  have integral : (2*Real.pi*Complex.I : ℂ)⁻¹ •
      (∮ z in C(c,R), (z-w)⁻¹ • (1 : A)-resolvent T z)=1-projector T c R := by
    rw [circleIntegral.integral_sub scalarInt resInt,circleIntegral.integral_smul_const,
      circleIntegral.integral_sub_inv_of_mem_ball hw,smul_sub,smul_smul,
      inv_mul_cancel₀ Complex.two_pi_I_ne_zero,one_smul]
    rfl
  constructor
  · change s*((2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ z in C(c,R), G z)=_
    have mapped : s*(∮ z in C(c,R), G z) = ∮ z in C(c,R), s*(G z) :=
      ContourProjectorContinuity.map_circleIntegral (ContinuousLinearMap.mul ℂ A s) G c R integrable
    rw [mul_smul_comm,mapped]
    rw [circleIntegral.integral_congr hR leftPoint]
    exact integral
  · change ((2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ z in C(c,R), G z)*s=_
    have mapped : (∮ z in C(c,R), G z)*s = ∮ z in C(c,R), (G z)*s :=
      ContourProjectorContinuity.map_circleIntegral ((ContinuousLinearMap.mul ℂ A).flip s) G c R integrable
    rw [smul_mul_assoc,mapped]
    rw [circleIntegral.integral_congr hR rightPoint]
    exact integral
end LeanShared.RieszCauchyShift
