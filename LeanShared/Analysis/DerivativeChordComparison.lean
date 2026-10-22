module
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! Chord inequalities pass to actual derivatives. This is useful when a
graph is specified geometrically before a smooth inverse projection exists. -/
public section
open Filter
open scoped Topology
namespace LeanShared.DerivativeChordComparison
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_deriv_le_of_chord {f : ℝ → F} {g : ℝ → G}
    {a : ℝ} {f' : F} {g' : G} {C : ℝ}
    (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (chord : ∀ᶠ t in 𝓝 a, ‖f t - f a‖ ≤ C * ‖g t - g a‖) :
    ‖f'‖ ≤ C * ‖g'‖ := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.norm
    (tendsto_const_nhds.mul hg.tendsto_slope.norm)
  filter_upwards [chord.filter_mono nhdsWithin_le_nhds] with t ht
  simpa only [slope_def_module, norm_smul, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left ht (norm_nonneg ((t - a)⁻¹))

theorem norm_fderiv_apply_le_of_chord {f : E → F} {g : E → G}
    {a : E} {f' : E →L[ℝ] F} {g' : E →L[ℝ] G} {C : ℝ}
    (hf : HasFDerivAt f f' a) (hg : HasFDerivAt g g' a)
    (chord : ∀ᶠ z in 𝓝 a, ‖f z - f a‖ ≤ C * ‖g z - g a‖)
    (v : E) : ‖f' v‖ ≤ C * ‖g' v‖ := by
  have curve : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have fc : HasDerivAt (fun t : ℝ => f (a + t • v)) (f' v) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (show HasFDerivAt f f' (a + (0 : ℝ) • v) by simpa using hf).comp_hasDerivAt 0 curve
  have gc : HasDerivAt (fun t : ℝ => g (a + t • v)) (g' v) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (show HasFDerivAt g g' (a + (0 : ℝ) • v) by simpa using hg).comp_hasDerivAt 0 curve
  have continuousCurve : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) := by
    simpa only [zero_smul, add_zero] using curve.continuousAt.tendsto
  apply norm_deriv_le_of_chord fc gc
  simpa only [zero_smul, add_zero] using continuousCurve.eventually chord

end LeanShared.DerivativeChordComparison
