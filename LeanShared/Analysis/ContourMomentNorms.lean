module

public import LeanShared.Analysis.WeakContourBound
public import LeanShared.Analysis.AnalyticResolvent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Positivity

/-! Strong and weak norm estimates for actual inverse resolvent moments.
The weak target may be incomplete. -/

public section
open ContinuousLinearMap Metric
namespace LeanShared.ContourMomentNorms
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scalar-dual bounds control the weak norm of an actual normalized contour. -/
theorem map_norm_le (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (r M : ℝ)
    (hr : 0 ≤ r) (hf : CircleIntegrable f c r)
    (bound : ∀ z ∈ sphere c r, ‖L (f z)‖ ≤ M) :
    ‖L (ContourProjectorContinuity.contour f c r)‖ ≤ r * M := by
  have zeroContour : ContourProjectorContinuity.contour (fun _ : ℂ => (0 : E)) c r = 0 := by
    unfold ContourProjectorContinuity.contour circleIntegral
    simp only [smul_zero, intervalIntegral.integral_zero]
  have estimate := WeakContourBound.norm_le L f (fun _ => 0) c r M hr hf
    (circleIntegrable_const 0 c r) (fun z hz => by simpa only [sub_zero] using bound z hz)
  simpa only [zeroContour, sub_zero] using estimate

/-- Scalar inverse weights on an outer contour have an explicit bound. -/
theorem inverse_weight_le (n : ℕ) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ ‖z‖) :
    ‖(z ^ n)⁻¹‖ ≤ (r ^ n)⁻¹ := by
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hr n) (pow_le_pow_left₀ hr.le hz n)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The actual inverse resolvent moment is circle integrable on any
resolvent contour lying outside a positive disk. -/
theorem integrable (T : E →L[ℂ] E) (n : ℕ) (c : ℂ) (r a : ℝ)
    (hr : 0 ≤ r) (ha : 0 < a) (lower : ∀ z ∈ sphere c r, a ≤ ‖z‖)
    (res : sphere c r ⊆ resolventSet ℂ T) :
    CircleIntegrable (fun z => (z ^ n)⁻¹ • resolvent T z) c r := by
  have nonzero : ∀ z ∈ sphere c r, z ^ n ≠ 0 := fun z hz =>
    pow_ne_zero n (norm_pos_iff.mp (ha.trans_le (lower z hz)))
  have continuousR : ContinuousOn (resolvent T) (sphere c r) := fun z hz =>
    (AnalyticResolvent.analyticAt T (res hz)).continuousAt.continuousWithinAt
  exact (((continuousOn_id.pow n).inv₀ nonzero).smul continuousR).circleIntegrable hr

/-- Strong operator norm of the actual inverse resolvent moment. -/
theorem strong_bound (T : E →L[ℂ] E) (n : ℕ) (c : ℂ) (r a L : ℝ)
    (hr : 0 ≤ r) (ha : 0 < a) (lower : ∀ z ∈ sphere c r, a ≤ ‖z‖)
    (res : sphere c r ⊆ resolventSet ℂ T) (normR : ∀ z ∈ sphere c r, ‖resolvent T z‖ ≤ L) :
    ‖ContourProjectorContinuity.contour (fun z => (z ^ n)⁻¹ • resolvent T z) c r‖ ≤
      r * ((a ^ n)⁻¹ * L) := by
  apply map_norm_le (ContinuousLinearMap.id ℂ (E →L[ℂ] E)) _ c r _ hr
    (integrable T n c r a hr ha lower res)
  intro z hz
  change ‖(z ^ n)⁻¹ • resolvent T z‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul (inverse_weight_le n a ha z (lower z hz)) (normR z hz)
    (norm_nonneg _) (by positivity)

/-- Weak pointwise norm of the actual inverse resolvent moment, requiring
no completeness of the weak target. -/
theorem weak_bound (T : E →L[ℂ] E) (i : E →L[ℂ] W) (n : ℕ) (c : ℂ) (r a η B : ℝ)
    (hr : 0 ≤ r) (ha : 0 < a)
    (lower : ∀ z ∈ sphere c r, a ≤ ‖z‖) (res : sphere c r ⊆ resolventSet ℂ T)
    (weakR : ∀ z ∈ sphere c r, ∀ y, ‖i ((resolvent T z) y)‖ ≤ η * ‖y‖ + B * ‖i y‖)
    (x : E) :
    ‖i ((ContourProjectorContinuity.contour (fun z => (z ^ n)⁻¹ • resolvent T z) c r) x)‖ ≤
      r * ((a ^ n)⁻¹ * (η * ‖x‖ + B * ‖i x‖)) := by
  apply map_norm_le (i.comp (ContinuousLinearMap.apply ℂ E x)) _ c r _ hr
    (integrable T n c r a hr ha lower res)
  intro z hz
  change ‖i (((z ^ n)⁻¹ • resolvent T z) x)‖ ≤ _
  rw [smul_apply, map_smul, norm_smul]
  exact mul_le_mul (inverse_weight_le n a ha z (lower z hz)) (weakR z hz x)
    (norm_nonneg _) (by positivity)

end LeanShared.ContourMomentNorms
