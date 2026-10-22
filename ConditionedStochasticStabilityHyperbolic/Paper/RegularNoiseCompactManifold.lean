module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

/-! The supplied finite Whitney atlas already implies compactness of the
actual manifold: its relatively compact patches cover every point. -/
public section
open Set
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] {T : M → M}

theorem WhitneyAtlas.compact_univ (A : WhitneyAtlas (E := E) T) :
    IsCompact (univ : Set M) := by
  have compact := isCompact_iUnion A.patch_compact
  apply compact.of_isClosed_subset isClosed_univ
  intro x _
  have covered : x ∈ ⋃ i, A.patch i := by rw [A.patch_cover]; exact mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp covered
  exact mem_iUnion.mpr ⟨i, subset_closure hi⟩

theorem WhitneyAtlas.compactSpace (A : WhitneyAtlas (E := E) T) : CompactSpace M :=
  ⟨A.compact_univ⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
