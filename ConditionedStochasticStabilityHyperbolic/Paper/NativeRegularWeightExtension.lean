module
public import LeanShared.Geometry.SmoothWeightCutoff
public import LeanShared.Geometry.SmoothFractionalRegularity

/-! A weight whose products with smooth cutoffs supported near a compact set are regular agrees,
on an open neighborhood of that set, with a globally regular nonnegative weight bounded by it. -/

public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeRegularWeightExtension
open LeanShared

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]

theorem exists_regular_extension (q : ℝ) (Λ W : Set M) (hΛ : IsCompact Λ) (hW : IsOpen W)
    (hΛW : Λ ⊆ W) (w : M → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (ζ * w)) :
    ∃ O : Set M, IsOpen O ∧ Λ ⊆ O ∧ ∃ gp : M → ℝ,
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q gp ∧ (∀ x, 0 ≤ gp x) ∧
      (∀ x, gp x ≤ w x) ∧ (∀ x ∈ O, gp x = w x) ∧ tsupport gp ⊆ W := by
  have hnh : W ∈ 𝓝ˢ Λ := mem_nhdsSet_iff_exists.mpr ⟨W, hW, hΛW, subset_rfl⟩
  obtain ⟨O, hO, hΛO, hOW⟩ := hΛ.exists_isOpen_closure_subset hnh
  obtain ⟨ζ, hζ, bounds, support, one⟩ := SmoothWeightCutoff.exists_cutoff (E := E) (closure O) W
    isClosed_closure.isCompact hW hOW
  refine ⟨O, hO, hΛO, ζ * w, smoothProduct ζ hζ support,
    fun x => mul_nonneg (bounds x).1 (hw0 x),
    fun x => mul_le_of_le_one_left (hw0 x) (bounds x).2, fun x hx => ?_,
    tsupport_mul_subset_left.trans support⟩
  change ζ x * w x = w x
  rw [one x (subset_closure hx), one_mul]

end ConditionedStochasticStabilityHyperbolic.Paper.NativeRegularWeightExtension
