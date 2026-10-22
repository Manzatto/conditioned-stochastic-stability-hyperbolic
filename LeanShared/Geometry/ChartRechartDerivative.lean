module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Exact germ and derivative identities between genuine chart expressions.
The partial chart inverses are used only on their valid open domains. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold
namespace LeanShared.ChartRechartDerivative
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 omit [NormedSpace ℝ E] [ChartedSpace E M] in
 theorem germ (c d e h:OpenPartialHomeomorph M E) {f:M→M} (continuous:Continuous f)
    {x:E} (hc:x∈c.target) (he:c.symm x∈e.source) (hh:f (c.symm x)∈h.source) :
    (d∘f∘c.symm)=ᶠ[𝓝 x] ((d∘h.symm)∘(h∘f∘e.symm)∘(e∘c.symm)) :=by
  have first:c.symm ⁻¹' e.source∈𝓝 x:=
    (c.continuousAt_symm hc).preimage_mem_nhds (e.open_source.mem_nhds he)
  have last:(f∘c.symm) ⁻¹' h.source∈𝓝 x:=
    (continuous.continuousAt.comp (c.continuousAt_symm hc)).preimage_mem_nhds
      (h.open_source.mem_nhds hh)
  filter_upwards [first,last] with y hy hy'
  change d (f (c.symm y))=d (h.symm (h (f (e.symm (e (c.symm y))))))
  have target:f (c.symm y)∈h.source:=hy'
  rw [e.left_inv hy,h.left_inv target]

 omit [ChartedSpace E M] in
 theorem fderiv_eq (c d e h:OpenPartialHomeomorph M E) {f:M→M} (continuous:Continuous f)
    {x:E} (hc:x∈c.target) (he:c.symm x∈e.source) (hh:f (c.symm x)∈h.source) :
    fderiv ℝ (d∘f∘c.symm) x=
      fderiv ℝ ((d∘h.symm)∘(h∘f∘e.symm)∘(e∘c.symm)) x :=
  (germ c d e h continuous hc he hh).fderiv_eq
end LeanShared.ChartRechartDerivative
