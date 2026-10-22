module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-! Pull back a genuine smooth manifold through an actual homeomorphism.
The new charts are explicit compositions with that homeomorphism. Their
transition maps are the original smooth transition maps, so both directions
of the homeomorphism become smooth without a new regularity assumption. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.HomeomorphTransportManifold

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace E N]

@[instance_reducible] def charts (h : M ≃ₜ N) : ChartedSpace E M where
  atlas := (fun c : OpenPartialHomeomorph N E => h.toOpenPartialHomeomorph.trans c) '' atlas E N
  chartAt x := h.toOpenPartialHomeomorph.trans (chartAt E (h x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt E (h x), chart_mem_atlas E (h x), rfl⟩

omit [NormedSpace ℝ E] in
@[simp] theorem chartAt_eq (h : M ≃ₜ N) (x : M) :
    (letI := charts (E := E) h; chartAt E x) =
      h.toOpenPartialHomeomorph.trans (chartAt E (h x)) := rfl

theorem manifold (h : M ≃ₜ N) [IsManifold (𝓘(ℝ, E)) ∞ N] :
    letI := charts (E := E) h; IsManifold (𝓘(ℝ, E)) ∞ M := by
  let := charts (E := E) h
  apply isManifold_of_contDiffOn (𝓘(ℝ, E)) ∞ M
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have compatible := ((contDiffGroupoid ∞ (𝓘(ℝ, E))).compatible hc hd).1
  simpa [contDiffPregroupoid, mfld_simps, Function.comp_def, Set.preimage, Set.inter_def] using compatible

theorem smooth (h : M ≃ₜ N) [IsManifold (𝓘(ℝ, E)) ∞ N] :
    letI := charts (E := E) h; ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ h := by
  let transported := charts (E := E) h
  let geometry := manifold (E := E) h
  rw [contMDiff_iff]
  refine ⟨h.continuous, fun x y => ?_⟩
  have compatible := ((contDiffGroupoid ∞ (𝓘(ℝ, E))).compatible
    (chart_mem_atlas E (h x)) (chart_mem_atlas E y)).1
  simpa [chartAt_eq, extChartAt, contDiffPregroupoid, mfld_simps,
    Function.comp_def, Set.preimage, Set.inter_def] using compatible

theorem smooth_symm (h : M ≃ₜ N) [IsManifold (𝓘(ℝ, E)) ∞ N] :
    letI := charts (E := E) h; ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ h.symm := by
  let transported := charts (E := E) h
  let geometry := manifold (E := E) h
  rw [contMDiff_iff]
  refine ⟨h.symm.continuous, fun x y => ?_⟩
  have compatible := ((contDiffGroupoid ∞ (𝓘(ℝ, E))).compatible
    (chart_mem_atlas E x) (chart_mem_atlas E (h y))).1
  simpa [chartAt_eq, extChartAt, contDiffPregroupoid, mfld_simps,
    Function.comp_def, Set.preimage, Set.inter_def] using compatible

/-- A concrete diffeomorphism to the original smooth manifold, with the
same underlying homeomorphism used to construct the pulled-back charts. -/
def diffeomorph (h : M ≃ₜ N) [IsManifold (𝓘(ℝ, E)) ∞ N] :
    letI := charts (E := E) h; M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N := by
  letI := charts (E := E) h
  exact { h.toEquiv with contMDiff_toFun := smooth (E := E) h, contMDiff_invFun := smooth_symm (E := E) h }

end LeanShared.HomeomorphTransportManifold
