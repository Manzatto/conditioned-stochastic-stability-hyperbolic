module

public import LeanShared.Geometry.LinearRechartedManifold

/-! Smooth maximal charts remain genuine maximal charts after the explicitly
constructed linear change of coordinate model. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.LinearRechartedManifold

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

def chartImage (e : E ≃L[ℝ] F) (c : OpenPartialHomeomorph M E) :
    OpenPartialHomeomorph M F := c.trans e.toHomeomorph.toOpenPartialHomeomorph

omit [ChartedSpace E M] in
private theorem transition_smooth (e : E ≃L[ℝ] F) (c d : OpenPartialHomeomorph M E)
    (hb : ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source) :
    ContDiffOn ℝ ∞ ((chartImage e c).symm.trans (chartImage e d))
      ((chartImage e c).symm.trans (chartImage e d)).source := by
  have hs : MapsTo e.symm
      (((c.trans e.toHomeomorph.toOpenPartialHomeomorph).symm.trans
        (d.trans e.toHomeomorph.toOpenPartialHomeomorph)).source)
      (c.symm.trans d).source := by
    intro v hv
    simpa only [mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph] using hv
  have hh := e.contDiff.comp_contDiffOn (hb.comp e.symm.contDiff.contDiffOn hs)
  simpa only [chartImage, mfld_simps, Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.coe_symm_toHomeomorph] using hh

omit [ChartedSpace E M] in
private theorem transition_mem (e : E ≃L[ℝ] F) (c d : OpenPartialHomeomorph M E)
    (h : c.symm.trans d ∈ contDiffGroupoid ∞ (𝓘(ℝ, E))) :
    (chartImage e c).symm.trans (chartImage e d) ∈ contDiffGroupoid ∞ (𝓘(ℝ, F)) := by
  constructor
  · have hb : ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source := by
      simpa only [contDiffPregroupoid, mfld_simps] using h.1
    simpa only [contDiffPregroupoid, mfld_simps] using transition_smooth e c d hb
  · have hb : ContDiffOn ℝ ∞ (d.symm.trans c) (d.symm.trans c).source := by
      simpa only [contDiffPregroupoid, mfld_simps] using h.2
    simpa only [contDiffPregroupoid, mfld_simps] using transition_smooth e d c hb

/-- Any ordinary maximal chart, not merely a preferred chartAt, is carried
to the maximal atlas of the constructed new smooth structure. -/
theorem chartImage_mem_maximal (e : E ≃L[ℝ] F) [IsManifold (𝓘(ℝ, E)) ∞ M]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) :
    letI := charts (M := M) e;
      chartImage e c ∈ maximalAtlas (𝓘(ℝ, F)) ∞ M := by
  let := charts (M := M) e
  change ∀ d ∈ (charts (M := M) e).atlas,
    (chartImage e c).symm.trans d ∈ contDiffGroupoid ∞ (𝓘(ℝ, F)) ∧
      d.symm.trans (chartImage e c) ∈ contDiffGroupoid ∞ (𝓘(ℝ, F))
  rintro _ ⟨d, hd, rfl⟩
  have hh := hc d hd
  exact ⟨transition_mem e c d hh.1, transition_mem e d c hh.2⟩

end LeanShared.LinearRechartedManifold
