module

public import LeanShared.Analysis.ResolventIdentity
public import LeanShared.Analysis.ContourProjectorContinuity
import all LeanShared.Analysis.ContourProjectorContinuity
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-! Idempotence of the operator-valued Riesz contour integral from genuine
resolvent separation. No finite-rank or projector premise is assumed. -/

public noncomputable section
open Filter Set Metric
open scoped Topology
namespace LeanShared.RieszContourIdempotent
open ContourProjectorContinuity
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The actual contour integral defining the spectral projector. -/
def projector (a : A) (c : ℂ) (R : ℝ) : A := contour (resolvent a) c R

/-- The Cauchy transform of the resolvent on the outer circle. -/
def cauchyTransform (a : A) (c : ℂ) (R : ℝ) (z : ℂ) : A :=
  contour (fun w => (w - z)⁻¹ • resolvent a w) c R

private theorem continuous_resolvent (a : A) (S : Set ℂ) (hS : S ⊆ resolventSet ℂ a) :
    ContinuousOn (resolvent a) S := fun _z hz =>
  (spectrum.hasDerivAt_resolvent_const_left (hS hz)).continuousAt.continuousWithinAt

/-- Resolvent multiplication by the contour projector, before idempotence. -/
theorem resolvent_mul_projector (a : A) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (sphereRes : sphere c R ⊆ resolventSet ℂ a) (z : ℂ) (hz : z ∈ ball c R)
    (hzRes : z ∈ resolventSet ℂ a) :
    resolvent a z * projector a c R = resolvent a z - cauchyTransform a c R z := by
  have different : ∀ w ∈ sphere c R, w ≠ z := by
    intro w hw he
    subst w
    exact (ne_of_lt hz) hw
  have scalarContinuous : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere c R) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (different w hw))
  have resolventContinuous := continuous_resolvent a (sphere c R) sphereRes
  have integrable : CircleIntegrable (resolvent a) c R :=
    resolventContinuous.circleIntegrable hR.le
  have scalarIntegrable : CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • resolvent a z) c R :=
    (scalarContinuous.smul continuousOn_const).circleIntegrable hR.le
  have productIntegrable : CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • resolvent a w) c R :=
    (scalarContinuous.smul resolventContinuous).circleIntegrable hR.le
  calc
    resolvent a z * projector a c R =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(c, R), resolvent a z * resolvent a w := by
      unfold projector contour
      rw [mul_smul_comm]
      congr 1
      exact map_circleIntegral (ContinuousLinearMap.mul ℂ A (resolvent a z))
        (resolvent a) c R integrable
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ w in C(c, R), (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
      congr 1
      exact circleIntegral.integral_congr hR.le
        (fun w hw => ResolventIdentity.first a z w hzRes (sphereRes hw) (different w hw))
    _ = resolvent a z - cauchyTransform a c R z := by
      simp_rw [smul_sub]
      rw [circleIntegral.integral_sub scalarIntegrable productIntegrable,
        circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hz,
        smul_sub, smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
      rfl

/-- The Cauchy transform has zero integral on any strictly smaller circle. -/
theorem cauchyTransform_integral_zero (a : A) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (sphereRes : sphere c R ⊆ resolventSet ℂ a) :
    (∮ z in C(c, r), cauchyTransform a c R z) = 0 := by
  have integrable : CircleIntegrable (resolvent a) c R :=
    (continuous_resolvent a (sphere c R) sphereRes).circleIntegrable (hr.le.trans hrR.le)
  have derivative : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (cauchyTransform a c R) z := by
    intro z hz
    have notSphere : z ∉ sphere c |R| := by
      rw [abs_of_pos (hr.trans hrR)]
      intro hs
      exact (ne_of_lt (hz.trans_lt hrR)) hs
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul integrable notSphere).const_smul
      (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    (fun z hz => (derivative z hz).continuousAt.continuousWithinAt)
    (fun z hz => derivative z (ball_subset_closedBall hz.1))

/-- A genuine resolvent annulus yields an idempotent spectral projector. -/
theorem idempotent (a : A) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (annulus : closedBall c R \ ball c r ⊆ resolventSet ℂ a) :
    projector a c r * projector a c r = projector a c r := by
  have innerSphere : sphere c r ⊆ resolventSet ℂ a := by
    intro z hz
    exact annulus ⟨(sphere_subset_closedBall hz).trans hrR.le, by
      intro h; exact (ne_of_lt h) hz⟩
  have outerSphere : sphere c R ⊆ resolventSet ℂ a := by
    intro z hz
    exact annulus ⟨sphere_subset_closedBall hz, by intro h; exact (ne_of_lt (h.trans hrR)) hz⟩
  have sameIntegral : (∮ z in C(c, R), resolvent a z) = ∮ z in C(c, r), resolvent a z :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR.le countable_empty
      (continuous_resolvent a _ annulus)
      (fun z hz => (spectrum.hasDerivAt_resolvent_const_left
        (annulus ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩)).differentiableAt)
  have same : projector a c R = projector a c r := by unfold projector contour; rw [sameIntegral]
  have innerIntegrable : CircleIntegrable (resolvent a) c r :=
    (continuous_resolvent a _ innerSphere).circleIntegrable hr.le
  have transformContinuous : ContinuousOn (cauchyTransform a c R) (sphere c r) := by
    intro z hz
    have hnot : z ∉ sphere c |R| := by
      rw [abs_of_pos (hr.trans hrR)]
      intro he
      exact hrR.ne (hz.symm.trans he)
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul
      ((continuous_resolvent a _ outerSphere).circleIntegrable (hr.le.trans hrR.le)) hnot).const_smul
        (2 * Real.pi * Complex.I : ℂ)⁻¹).continuousAt.continuousWithinAt
  calc
    projector a c r * projector a c r = projector a c r * projector a c R := by rw [same]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(c, r), resolvent a z * projector a c R := by
      unfold projector contour
      rw [smul_mul_assoc]
      congr 1
      exact map_circleIntegral ((ContinuousLinearMap.mul ℂ A).flip (contour (resolvent a) c R))
        (resolvent a) c r innerIntegrable
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(c, r), resolvent a z - cauchyTransform a c R z := by
      congr 1
      exact circleIntegral.integral_congr hr.le (fun z hz =>
        resolvent_mul_projector a c R (hr.trans hrR) outerSphere z
          (hz.trans_lt hrR) (innerSphere hz))
    _ = projector a c r := by
      rw [circleIntegral.integral_sub innerIntegrable (transformContinuous.circleIntegrable hr.le),
        cauchyTransform_integral_zero a c r R hr hrR outerSphere, sub_zero]
      rfl

end LeanShared.RieszContourIdempotent
