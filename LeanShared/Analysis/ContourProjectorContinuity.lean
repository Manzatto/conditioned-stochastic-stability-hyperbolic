module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! Bounded linear maps commute with operator-valued circle projectors.
Uniform weak resolvent estimates imply quantitative weak projector estimates
and convergence. These are the contour-integration step of KL, separated
from its deeper weak-resolvent stability estimate. -/

public noncomputable section
open Filter Metric
open scoped Topology
namespace LeanShared.ContourProjectorContinuity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Bounded linear maps commute with the literal circle integral. -/
theorem map_circleIntegral (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) :
    L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  have hh := L.intervalIntegral_comp_comm hf.out
  simpa only [map_smul] using hh.symm

/-- The normalized contour integral used to construct a Riesz projector. -/
def contour (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), f z

/-- Exact weak-space image of a difference of contour projectors. -/
theorem map_contour_sub (L : E →L[ℂ] F) (f g : ℂ → E) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    L (contour f c R - contour g c R) = contour (fun z => L (f z - g z)) c R := by
  unfold contour
  rw [← smul_sub, ← circleIntegral.integral_sub hf hg, map_smul,
    map_circleIntegral L (fun z => f z - g z) c R (hf.sub hg)]

/-- The contour length cancels the normalization: the projector difference
is bounded by the circle radius times the uniform weak resolvent error. -/
theorem norm_map_contour_sub_le (L : E →L[ℂ] F) (f g : ℂ → E)
    (c : ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
    (bound : ∀ z ∈ sphere c R, ‖L (f z - g z)‖ ≤ M) :
    ‖L (contour f c R - contour g c R)‖ ≤ R * M := by
  rw [map_contour_sub L f g c R hf hg]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR bound

/-- Weak resolvent convergence on the contour yields weak projector
convergence for arbitrary parameter filters. -/
theorem tendsto_map_contour_sub {ι : Type*} {l : Filter ι}
    (L : E →L[ℂ] F) (f : ι → ℂ → E) (g : ℂ → E) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hg : CircleIntegrable g c R) (modulus : ι → ℝ)
    (converges : Tendsto modulus l (𝓝 0))
    (estimates : ∀ᶠ ε in l, CircleIntegrable (f ε) c R ∧
      ∀ z ∈ sphere c R, ‖L (f ε z - g z)‖ ≤ modulus ε) :
    Tendsto (fun ε => L (contour (f ε) c R - contour g c R)) l (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using converges.const_mul R)
  filter_upwards [estimates] with ε hε
  exact norm_map_contour_sub_le L (f ε) g c R (modulus ε) hR hε.1 hg hε.2

end LeanShared.ContourProjectorContinuity
