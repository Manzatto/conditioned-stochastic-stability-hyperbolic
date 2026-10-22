module
public import LeanShared.Geometry.PseudoReferenceCoordinateMaps

/-! Actual ambient compact patches for the constructed pseudo-reference
chart index, with explicit chart-source margins and selected membership. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
  (d : HyperbolicBasicSet.PseudoReferenceGeometry h)

@[expose] def ambientPatch (i : Λ) : Set M := by
  classical
  exact if i ∈ d.centers then Subtype.val '' d.patch i else ∅

theorem compact_ambientPatch (i : Λ) : IsCompact (ambientPatch d i) := by
  classical
  by_cases hi : i ∈ d.centers
  · simpa only [ambientPatch,ite_eq_left hi] using (d.compact_patch i).image continuous_subtype_val
  · simp only [ambientPatch,ite_eq_right hi,isCompact_empty]

theorem ambientPatch_source (i : Λ) : ambientPatch d i ⊆ (chartAt E i.val).source := by
  classical
  by_cases hi : i ∈ d.centers
  · rintro x hx
    rw [ambientPatch,ite_eq_left hi] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact d.chart_source i hi y hy
  · simp only [ambientPatch,ite_eq_right hi,empty_subset]

theorem selected_ambientPatch (x : Λ) : x.val ∈ ambientPatch d (d.index x) := by
  rw [ambientPatch,ite_eq_left (d.index_mem x)]
  exact ⟨x,d.selected_patch x,rfl⟩

end LeanShared.PseudoReferenceCoordinateMaps
