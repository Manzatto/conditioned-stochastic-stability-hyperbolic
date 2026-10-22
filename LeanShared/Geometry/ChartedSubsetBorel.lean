module
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A subset carrying a locally compact manifold atlas is Borel in a
second-countable Hausdorff ambient space. No immersion or area theorem is
needed: the subtype is sigma compact and its inclusion has compact images. -/
public section
open Set MeasureTheory
namespace LeanShared.ChartedSubsetBorel

theorem measurableSet_of_charted
    {X H : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace H] [LocallyCompactSpace H]
    (S : Set X) [ChartedSpace H S] : MeasurableSet S := by
  let : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  have : SigmaCompactSpace S := inferInstance
  have compactRange : IsSigmaCompact (range (Subtype.val : S → X)) :=
    isSigmaCompact_range continuous_subtype_val
  obtain ⟨K, compact, covers⟩ := compactRange
  have measurable : MeasurableSet (⋃ n, K n) :=
    MeasurableSet.iUnion (fun n => (compact n).isClosed.measurableSet)
  simpa only [covers, Subtype.range_coe] using measurable

end LeanShared.ChartedSubsetBorel
