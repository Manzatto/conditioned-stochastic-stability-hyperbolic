module
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Actual precompact smoothing regions inside genuine chart targets.
The regions also retain the original open manifold support restriction;
their closures stay inside the chart, so completion never crosses a
chart boundary. -/
public noncomputable section
open Set Metric
namespace LeanShared.ChartSmoothingRegions
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]

theorem exists_region (e : OpenPartialHomeomorph M E) {K : Set E}
    (compact : IsCompact K) (target : K ⊆ e.target) {V : Set M} (openV : IsOpen V) :
    ∃ W : Set E, IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ e.target ∧
      (∀ y ∈ W, e.symm y ∈ V) ∧ K ∩ e.symm ⁻¹' V ⊆ W := by
  obtain ⟨δ, hδ, safe⟩ := compact.exists_cthickening_subset_open e.open_target target
  let O := thickening δ K
  let W := O ∩ (e.target ∩ e.symm ⁻¹' V)
  have compactO : IsCompact (closure O) := compact.cthickening.of_isClosed_subset
    isClosed_closure (closure_thickening_subset_cthickening δ K)
  have safeO : closure O ⊆ e.target := (closure_thickening_subset_cthickening δ K).trans safe
  refine ⟨W, isOpen_thickening.inter (e.isOpen_inter_preimage_symm openV),
    compactO.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left),
    (closure_mono inter_subset_left).trans safeO, fun y hy => hy.2.2, ?_⟩
  intro y hy
  exact ⟨self_subset_thickening hδ K hy.1, target hy.1, hy.2⟩

structure Data (e : I → OpenPartialHomeomorph M E) (K : I → Set E) (V : Set M) where
  region : I → Set E
  open_region : ∀ i, IsOpen (region i)
  compact_closure : ∀ i, IsCompact (closure (region i))
  closure_target : ∀ i, closure (region i) ⊆ (e i).target
  inverse_region : ∀ i y, y ∈ region i → (e i).symm y ∈ V
  contains : ∀ i, K i ∩ (e i).symm ⁻¹' V ⊆ region i

@[expose] def data (e : I → OpenPartialHomeomorph M E) (K : I → Set E)
    (compact : ∀ i, IsCompact (K i)) (target : ∀ i, K i ⊆ (e i).target)
    {V : Set M} (openV : IsOpen V) : Data e K V := by
  classical
  choose W openW compactW targetW inverseW containsW using
    fun i => exists_region (e i) (compact i) (target i) openV
  exact ⟨W, openW, compactW, targetW, inverseW, containsW⟩
end LeanShared.ChartSmoothingRegions
