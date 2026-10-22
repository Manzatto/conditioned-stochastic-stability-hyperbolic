module

public import LeanShared.Analysis.ContourProjectorContinuity
public import Mathlib.Analysis.Normed.Module.HahnBanach
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Weak contour estimates remain valid for an incomplete target space,
using scalar Hahn–Banach tests rather than a Bochner integral in that space. -/

public section
open Filter Metric Topology
namespace LeanShared.WeakContourBound
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Uniform weak resolvent bounds control actual contour differences even
when the weak target is incomplete. -/
theorem norm_le (L : E →L[ℂ] F) (f g : ℂ → E) (c : ℂ) (r M : ℝ)
    (hr : 0 ≤ r) (hf : CircleIntegrable f c r) (hg : CircleIntegrable g c r)
    (bound : ∀ z ∈ sphere c r, ‖L (f z - g z)‖ ≤ M) :
    ‖L (ContourProjectorContinuity.contour f c r -
      ContourProjectorContinuity.contour g c r)‖ ≤ r * M := by
  let v := L (ContourProjectorContinuity.contour f c r - ContourProjectorContinuity.contour g c r)
  obtain ⟨φ, hφnorm, hφv⟩ := exists_dual_vector'' ℂ v
  have scalar := ContourProjectorContinuity.norm_map_contour_sub_le (φ.comp L) f g c r M hr hf hg
    (fun z hz => ((φ.le_opNorm _).trans (by
      exact (mul_le_of_le_one_left (norm_nonneg _) hφnorm).trans (bound z hz))))
  change ‖φ v‖ ≤ r * M at scalar
  rw [hφv] at scalar
  change ‖(‖v‖ : ℂ)‖ ≤ r * M at scalar
  rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v)] at scalar
  exact scalar

/-- Uniform weak convergence on the contour gives actual weak-projector
convergence, without a completeness hypothesis on the weak target. -/
theorem tendsto {l : Filter I} (L : E →L[ℂ] F) (f : I → ℂ → E) (g : ℂ → E)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hg : CircleIntegrable g c r)
    (integrable : ∀ᶠ ε in l, CircleIntegrable (f ε) c r)
    (converges : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in l, ∀ z ∈ sphere c r,
      ‖L (f ε z - g z)‖ ≤ δ) :
    Tendsto (fun ε => L (ContourProjectorContinuity.contour (f ε) c r -
      ContourProjectorContinuity.contour g c r)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have htol : 0 < δ / (r + 1) := div_pos hδ (by positivity)
  filter_upwards [integrable, converges (δ / (r + 1)) htol] with ε hint hbound
  rw [dist_zero_right]
  apply (norm_le L (f ε) g c r (δ / (r + 1)) hr hint hg hbound).trans_lt
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0 < r + 1)).mpr
  nlinarith

end LeanShared.WeakContourBound
