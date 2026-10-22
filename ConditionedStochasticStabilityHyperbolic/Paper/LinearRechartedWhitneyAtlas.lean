module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Geometry.LinearRechartedAtlas

/-! Actual finite Whitney charts after a linear change of model. Patches,
compactness, and target control are preserved; the coordinate maps are the
literal linear conjugates. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared.LinearRechartedManifold

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {T : M → M} (e : E ≃L[ℝ] F) (A : WhitneyAtlas (E := E) T)

/-- Every chart is explicitly composed with the same linear equivalence. -/
def WhitneyAtlas.linearRechart : letI := charts (M := M) e; WhitneyAtlas (E := F) T := by
  letI := charts (M := M) e
  exact {
  count := A.count
  source i := chartImage e (A.source i)
  target i := chartImage e (A.target i)
  source_smooth i := chartImage_mem_maximal e (A.source i) (A.source_smooth i)
  target_smooth i := chartImage_mem_maximal e (A.target i) (A.target_smooth i)
  patch := A.patch
  patch_open := A.patch_open
  patch_cover := A.patch_cover
  patch_compact := A.patch_compact
  patch_source i := by simpa only [chartImage, mfld_simps] using A.patch_source i
  deterministic_target i := by
    simpa only [chartImage, mfld_simps] using A.deterministic_target i }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The exact finite chart formula used by ordinary fractional norm
transport. The actual map and its parameter family remain unchanged. -/
theorem WhitneyAtlas.linearRechart_coordinate (f : M → M) (i : Fin A.count) (v : F) :
    letI := charts (M := M) e;
    (A.linearRechart e).coordinate f i v = e (A.coordinate f i (e.symm v)) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem WhitneyAtlas.linearRechart_coordinatePatch (i : Fin A.count) :
    letI := charts (M := M) e;
    (A.linearRechart e).coordinatePatch i = e '' (A.coordinatePatch i) := by
  let := charts (M := M) e
  rw [e.image_eq_preimage_symm]
  ext v
  simp only [WhitneyAtlas.coordinatePatch, WhitneyAtlas.linearRechart, chartImage,
    mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
