module

public import LeanShared.Analysis.CompactTwoNormMeromorphicResolvent
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! Translating an operator by a scalar translates its actual Riesz contour
by the same scalar, without spectral assumptions. -/

public section
namespace LeanShared.ShiftedContour
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Exact centre-translation formula for actual contour projectors. -/
theorem formula (T : A) (c : ℂ) (r : ℝ) :
    RieszContourIdempotent.projector (T - c • 1) 0 r =
      RieszContourIdempotent.projector T c r := by
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(0, r), resolvent (T - c • 1) z) =
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent T z)
  congr 1
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [deriv_circleMap, CompactTwoNormMeromorphicResolvent.shift_formula]
  congr 2
  simp only [circleMap, add_zero, add_comm]

end LeanShared.ShiftedContour
