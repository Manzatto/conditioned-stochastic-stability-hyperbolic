module

public import LeanShared.Geometry.TangentChartUniformBounds
public import LeanShared.Geometry.CompactChartPairCover

/-! A compact manifold set has a constructed finite cover by compact
native tangent-chart patches with ONE two-sided fiber-norm bound. The
chart family, patches and constant are outputs. -/
public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff Bundle BigOperators
namespace LeanShared.FiniteNativeTangentCharts
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

set_option maxHeartbeats 1000000 in
theorem exists_cover (K : Set M) (compact : IsCompact K) :
    ∃ centers : Finset K, ∃ patch : K → Set M, ∃ C > 0,
      (∀ i, IsCompact (patch i) ∧ patch i ⊆ (chartAt E i.val).source) ∧
      K ⊆ ⋃ i ∈ centers, interior (patch i) ∧
      ∀ i ∈ centers, ∀ x ∈ patch i,
        ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).continuousLinearMapAt ℝ x‖ ≤ C ∧
        ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).symmL ℝ x‖ ≤ C := by
  classical
  obtain ⟨centers, patch, facts, cover⟩ := CompactChartPairCover.exists_cover
    (E := E) (F := E) (id : M → M) continuous_id K compact
  have bounds (i : K) := TangentChartTrivialization.exists_bounds i.val (patch i)
    (facts i).1 (facts i).2.1
  choose A positiveA boundA using bounds
  let C := (∑ i ∈ centers, A i) + 1
  have sumNonnegative : 0 ≤ ∑ i ∈ centers, A i :=
    Finset.sum_nonneg (fun i _ => (positiveA i).le)
  have each (i : K) (hi : i ∈ centers) : A i ≤ C := by
    have below := Finset.single_le_sum (fun j _ => (positiveA j).le) hi
    exact below.trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨centers, patch, C, by dsimp [C]; linarith, fun i => ⟨(facts i).1, (facts i).2.1⟩,
    cover, ?_⟩
  intro i hi x hx
  exact ⟨((boundA i x hx).1).trans (each i hi), ((boundA i x hx).2).trans (each i hi)⟩

end LeanShared.FiniteNativeTangentCharts
