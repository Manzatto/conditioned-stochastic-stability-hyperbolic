module
public import LeanShared.Analysis.LocalSubmersionVolumeBound
public import Mathlib.Topology.Compactness.Compact

/-! Compact full-rank maps push forward finite-dimensional Haar volume to
a measure uniformly bounded by target Haar volume. Source and target may
have different dimensions. No injectivity, patch, or density source is supplied. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal BigOperators
namespace LeanShared.SubmersionLinearCoordinates

theorem exists_compact_submersion_volume_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (σ : Measure F) [μ.IsAddHaarMeasure] [σ.IsAddHaarMeasure]
    {f : E → F} {K : Set E} (compact : IsCompact K)
    (smooth : ∀ x ∈ K, ContDiffAt ℝ 1 f x)
    (rank : ∀ x ∈ K, Function.Surjective (fderiv ℝ f x)) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ (μ.restrict K).map f ≤ C • σ := by
  classical
  have localBound (x : K) :=
    exists_local_submersion_volume_bound μ σ (smooth x.val x.property) (rank x.val x.property)
  choose u openU member differentiable C finiteC bound using localBound
  have cover : K ⊆ ⋃ i : K, u i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, member ⟨x, hx⟩⟩
  obtain ⟨indices, subcover⟩ := compact.elim_finite_subcover u openU cover
  refine ⟨∑ i ∈ indices, C i, ?_, ?_⟩
  · exact (ENNReal.sum_lt_top.mpr (fun i _ => lt_top_iff_ne_top.mpr (finiteC i))).ne
  · apply Measure.le_iff.mpr
    intro A hA
    have baseMeas : AEMeasurable f (μ.restrict K) :=
      ContinuousOn.aemeasurable₀
        (fun x hx => (smooth x hx).continuousAt.continuousWithinAt) compact.measurableSet.nullMeasurableSet
    rw [Measure.map_apply_of_aemeasurable baseMeas hA,
      Measure.restrict_apply' compact.measurableSet, Measure.smul_apply, smul_eq_mul]
    calc
      μ (f ⁻¹' A ∩ K) ≤ μ (⋃ i ∈ indices, f ⁻¹' A ∩ u i) := by
        apply measure_mono
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp (subcover hx.2)
        obtain ⟨hindex, hu⟩ := mem_iUnion.mp hi
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hindex, hx.1, hu⟩⟩
      _ ≤ ∑ i ∈ indices, μ (f ⁻¹' A ∩ u i) := measure_biUnion_finset_le _ _
      _ = ∑ i ∈ indices, ((μ.restrict (u i)).map f) A := by
        apply Finset.sum_congr rfl
        intro i _
        have patchMeas : AEMeasurable f (μ.restrict (u i)) :=
          ContinuousOn.aemeasurable₀ (differentiable i).continuousOn (openU i).measurableSet.nullMeasurableSet
        rw [Measure.map_apply_of_aemeasurable patchMeas hA, Measure.restrict_apply' (openU i).measurableSet]
      _ ≤ ∑ i ∈ indices, C i * σ A :=
        Finset.sum_le_sum (fun i _ => bound i A)
      _ = (∑ i ∈ indices, C i) * σ A := (Finset.sum_mul _ _ _).symm
end LeanShared.SubmersionLinearCoordinates
