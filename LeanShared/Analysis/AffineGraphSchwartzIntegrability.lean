module
public import LeanShared.Analysis.ObliqueSchwartzDecay
public import LeanShared.Analysis.SchwartzAmbientRealization

/-! Integrability of every actual Schwartz function on every full affine
graph follows from its defining radial decay and the projection inequality. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.AffineGraphParameter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem schwartz_integrable (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ)
    (f : 𝓢(E,ℂ)) : Integrable (fun u => f (point U L v u)) := by
  let m := Module.finrank ℝ U+1
  have hr : (Module.finrank ℝ U:ℝ)<(m:ℝ) := Nat.cast_lt.mpr (Nat.lt_succ_self _)
  obtain ⟨D,hD,bound⟩ := SchwartzAmbientRealization.exists_decay f m
  have integrable := (GraphLeafNorm.integrable_radialWeight (volume : Measure U) hr).const_mul D
  have continuous : Continuous (fun u => f (point U L v u)) :=
    f.continuous.comp ((IntrinsicGraphJacobian.graphDifferential U L).continuous.add continuous_const)
  apply integrable.mono' continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have parameter : ‖u‖ ≤ ‖point U L v u‖ := by
    simpa only [projection_point] using U.norm_orthogonalProjectionOnto_apply_le (point U L v u)
  exact (bound _).trans (mul_le_mul_of_nonneg_left
    (GraphLeafNorm.radialWeight_antitone_norm (by positivity : (0:ℝ)≤(m:ℝ)) parameter) hD)
end LeanShared.AffineGraphParameter
