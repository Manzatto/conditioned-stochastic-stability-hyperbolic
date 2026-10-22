module
public import LeanShared.Geometry.CompactParametricInverseRegularity
public import Mathlib.Topology.Compactness.Compact

/-! A compact family of genuine invertible state maps has a common OPEN
parameter neighborhood on which its globally chosen inverses are C1 and
satisfy both inverse identities. The neighborhood and the inverse map are
constructed, not source fields. -/
public noncomputable section
namespace LeanShared.CompactParametricInverseDomain
open Set Filter IsManifold
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 2400000 in
theorem exists_domain
    {A E P M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace P] [ChartedSpace A P] [IsManifold (𝓘(ℝ,A)) ∞ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (F : P × M → M) (continuous : Continuous F) (K : Set P) (compact : IsCompact K) (default : M)
    (smooth : ∀ a ∈ K, ∀ x, ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F (a,x))
    (bijective : ∀ a ∈ K, Function.Bijective (fun z => F (a,z)))
    (rank : ∀ a ∈ K, ∀ x, Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => F (a,z)) x)) :
    ∃ U : Set P, IsOpen U ∧ K ⊆ U ∧
      ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1
        (CompactLocalInverseUniqueness.root F default) (U ×ˢ univ) ∧
      (∀ a ∈ U, ∀ y, F (a,CompactLocalInverseUniqueness.root F default (a,y)) = y) ∧
      ∀ a ∈ U, ∀ x, CompactLocalInverseUniqueness.root F default (a,F (a,x)) = x := by
  let inverse := CompactLocalInverseUniqueness.root F default
  let smoothSet : Set (P × M) := {p | ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 inverse p}
  let rightSet : Set (P × M) := {p | F (p.1,inverse p) = p.2}
  let leftSet : Set (P × M) := {p | inverse (p.1,F p) = p.2}
  have openSmooth : IsOpen smoothSet := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact (contMDiffAt_iff_contMDiffAt_nhds (by decide : (1 : ℕ∞ω) ≠ ∞)).mp hp
  have containsRight : K ×ˢ (univ : Set M) ⊆ smoothSet ∩ interior rightSet := by
    rintro ⟨a,y⟩ ⟨ha,_⟩
    obtain ⟨x,rfl⟩ := (bijective a ha).2 y
    have made := CompactParametricInverseRegularity.local_inverse F continuous a x default
      (smooth a ha x) (bijective a ha).1 (rank a ha x)
    exact ⟨made.1,mem_interior_iff_mem_nhds.mpr made.2.1⟩
  have containsLeft : K ×ˢ (univ : Set M) ⊆ interior leftSet := by
    rintro ⟨a,x⟩ ⟨ha,_⟩
    have made := CompactParametricInverseRegularity.local_inverse F continuous a x default
      (smooth a ha x) (bijective a ha).1 (rank a ha x)
    exact mem_interior_iff_mem_nhds.mpr made.2.2
  obtain ⟨U₁,V₁,openU₁,_openV₁,containsU₁,containsV₁,productRight⟩ :=
    generalized_tube_lemma compact isCompact_univ (openSmooth.inter isOpen_interior) containsRight
  obtain ⟨U₂,V₂,openU₂,_openV₂,containsU₂,containsV₂,productLeft⟩ :=
    generalized_tube_lemma compact isCompact_univ isOpen_interior containsLeft
  refine ⟨U₁ ∩ U₂,openU₁.inter openU₂,fun a ha => ⟨containsU₁ ha,containsU₂ ha⟩,?_,?_,?_⟩
  · intro p hp
    exact (productRight ⟨hp.1.1,containsV₁ (mem_univ p.2)⟩).1.contMDiffWithinAt
  · intro a ha y
    have member : (a,y) ∈ rightSet := interior_subset (productRight ⟨ha.1,containsV₁ (mem_univ y)⟩).2
    exact member
  · intro a ha x
    have member : (a,x) ∈ leftSet := interior_subset (productLeft ⟨ha.2,containsV₂ (mem_univ x)⟩)
    exact member

end LeanShared.CompactParametricInverseDomain
