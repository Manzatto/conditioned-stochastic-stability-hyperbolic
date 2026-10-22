module
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! Exact local reexpression of an actual map between two chart pairs. The
partial inverses are cancelled only on their genuine sources. -/
public noncomputable section
namespace LeanShared
open Set Filter
open scoped Topology

theorem chart_reexpression_germ
    {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (c d s t : OpenPartialHomeomorph M E) (f : M → M) (continuous : Continuous f)
    (v : E) (initial : v ∈ c.target) (first : c.symm v ∈ s.source)
    (last : f (c.symm v) ∈ t.source) :
    (d ∘ t.symm) ∘ (t ∘ f ∘ s.symm) ∘ (s ∘ c.symm) =ᶠ[𝓝 v]
      d ∘ f ∘ c.symm := by
  have nearFirst := (c.continuousAt_symm initial).eventually (s.open_source.mem_nhds first)
  have nearLast := (continuous.continuousAt.comp (c.continuousAt_symm initial)).eventually
    (t.open_source.mem_nhds last)
  filter_upwards [nearFirst, nearLast] with y hs ht
  change f (c.symm y) ∈ t.source at ht
  simp only [Function.comp_apply, s.left_inv hs, t.left_inv ht]

end LeanShared
