module
public import LeanShared.Topology.FiniteCompactNeighborhoodCover
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Finite compact ambient chart-pair patches for an actual continuous map.
No prechosen uniform chart or itinerary source is supplied. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.CompactChartPairCover
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [IsManifold (𝓘(ℝ,F)) ∞ N]

omit [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [IsManifold (𝓘(ℝ,F)) ∞ N] in
theorem exists_cover (H : M → N) (continuous : Continuous H)
    (K : Set M) (compact : IsCompact K) :
    ∃ centers : Finset K, ∃ patch : K → Set M,
      (∀ x, IsCompact (patch x) ∧ patch x ⊆ (chartAt E x.val).source ∧
        MapsTo H (patch x) (chartAt F (H x.val)).source ∧
        x.val ∈ interior (patch x)) ∧
      K ⊆ ⋃ x ∈ centers, interior (patch x) := by
  let U := fun x : M => (chartAt E x).source ∩ H ⁻¹' (chartAt F (H x)).source
  have openU (x : M) : IsOpen (U x) :=
    (chartAt E x).open_source.inter ((chartAt F (H x)).open_source.preimage continuous)
  have member (x : M) (_ : x ∈ K) : x ∈ U x :=
    ⟨mem_chart_source E x,mem_chart_source F (H x)⟩
  obtain ⟨centers,patch,facts,cover⟩ :=
    FiniteCompactNeighborhoodCover.exists_cover K compact U openU member
  exact ⟨centers,patch,fun x => ⟨(facts x).1,
    fun y hy => ((facts x).2.1 hy).1,
    fun y hy => ((facts x).2.1 hy).2,(facts x).2.2⟩,cover⟩
end LeanShared.CompactChartPairCover
