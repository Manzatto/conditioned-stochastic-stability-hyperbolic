module
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! A contour containing no spectrum has zero projector. A bounded invertible
block supplies the required genuine small resolvent disks automatically. -/
public noncomputable section
open Set Metric
namespace LeanShared.ResolventContourZero
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem eq_zero (B : A) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (res : closedBall c R ⊆ resolventSet ℂ B) : RieszContourIdempotent.projector B c R = 0 := by
  have derivative : ∀ z ∈ closedBall c R, DifferentiableAt ℂ (resolvent B) z :=
    fun z hz => (spectrum.hasDerivAt_resolvent_const_left (res hz)).differentiableAt
  have integral := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    (fun z hz => (derivative z hz).continuousAt.continuousWithinAt)
    (fun z hz => derivative z (ball_subset_closedBall hz.1))
  change (2*Real.pi*Complex.I : ℂ)⁻¹ • (∮ z in C(c,R), resolvent B z) = 0
  rw [integral, smul_zero]

theorem exists_zero_contours (B : A) (invertible : IsUnit B) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      closedBall (0 : ℂ) R ⊆ resolventSet ℂ B ∧ RieszContourIdempotent.projector B 0 R = 0 := by
  have zeroRes : (0 : ℂ) ∈ resolventSet ℂ B := by
    change IsUnit (algebraMap ℂ A 0 - B)
    simpa only [map_zero, zero_sub] using invertible.neg
  obtain ⟨r, positive, contained⟩ := Metric.isOpen_iff.mp (spectrum.isOpen_resolventSet B) 0 zeroRes
  refine ⟨r, positive, fun R hR hr => ?_⟩
  have res : closedBall (0 : ℂ) R ⊆ resolventSet ℂ B :=
    fun z hz => contained (lt_of_le_of_lt hz hr)
  exact ⟨res, eq_zero B 0 R hR.le res⟩
end LeanShared.ResolventContourZero
