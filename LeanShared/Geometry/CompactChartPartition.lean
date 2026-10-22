module

public import LeanShared.Geometry.FiniteChartLocalization
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Complex.Basic

/-!
# Constructed finite smooth chart partitions on a compact manifold

Compactness selects a finite genuine chart subcover. Mathlib's smooth
partition-of-unity theorem constructs the subordinate cutoffs. They are
converted to complex scalar cutoffs and have compact support automatically
on the compact manifold. Thus the localization constructor needs neither
a supplied finite partition nor a supplied global localization linear map.

The chart family may be the canonical smooth atlas or the actual adapted
atlas from classical hyperbolic cone geometry. The construction preserves
the selected charts and their source domains.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff BigOperators Topology

namespace LeanShared.CompactChartPartition

variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_partition (e : J → OpenPartialHomeomorph M E)
    (S : Set M) (hS : IsCompact S) (hcover : S ⊆ ⋃ j, (e j).source) :
    ∃ (s : Finset J) (θ : s → M → ℂ),
      (∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ (e i).source) ∧
      (∀ i, HasCompactSupport (θ i)) ∧
      (∀ x ∈ S, ∑ i, θ i x = 1) := by
  classical
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun j => (e j).source)
    (fun j => (e j).open_source) hcover
  have hselected : S ⊆ ⋃ i : s, (e i).source := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    hS.isClosed (fun i : s => (e i).source) (fun i => (e i).open_source) hselected
  let θ : s → M → ℂ := fun i x => Complex.ofRealCLM (ρ i x)
  refine ⟨s, θ, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Complex.ofRealCLM.contMDiff.comp (ρ i).contMDiff
  · intro i
    exact (tsupport_comp_subset (map_zero Complex.ofRealCLM) (ρ i)).trans (hρ i)
  · intro i
    exact HasCompactSupport.of_compactSpace (θ i)
  · intro x hx
    have hr : (∑ i : s, ρ i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    have hc := congrArg Complex.ofRealCLM hr
    simpa only [θ, map_sum, Complex.ofRealCLM_apply, Complex.ofReal_one] using hc

/-- On the whole compact manifold the canonical genuine atlas needs no
separate covering input. The resulting finite charts are smooth atlas
members, so the supported Schwartz localization constructor applies. -/
theorem exists_canonical_finite_partition :
    ∃ (s : Finset M) (θ : s → M → ℂ),
      (∀ i : s, chartAt E (i : M) ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) ∧
      (∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ (chartAt E (i : M)).source) ∧
      (∀ i, HasCompactSupport (θ i)) ∧
      (∀ x : M, ∑ i, θ i x = 1) := by
  obtain ⟨s, θ, hθ, hsupp, hcompact, hsum⟩ := exists_finite_partition
    (fun x : M => chartAt E x) Set.univ isCompact_univ (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  exact ⟨s, θ, fun i => chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) i.val,
    hθ, hsupp, hcompact, fun x => hsum x (mem_univ x)⟩

end LeanShared.CompactChartPartition
