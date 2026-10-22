module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import Mathlib.Topology.MetricSpace.Thickening

/-! Small noise keeps a compact set inside any open set that the reference
map sends it into: the actual noise maps are uniformly close to `T`. -/
public noncomputable section
open Set Metric
open scoped NNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
theorem Maps.exists_capture_window (F : Maps (E := E) (ι := ι) T r) {K U : Set M}
    (compact : IsCompact K) (openU : IsOpen U) (into : ∀ x ∈ K, T x ∈ U) :
    ∃ w : ℝ≥0, 0 < w ∧ w ≤ F.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ w →
      ∀ control : cube (ι := ι) ε, ∀ x ∈ K, F.family ε control.val x ∈ U := by
  have image : IsCompact ((T : M → M) '' K) := compact.image T.continuous
  obtain ⟨δ, positiveδ, inside⟩ :=
    image.exists_thickening_subset_open openU (by rintro _ ⟨x, hx, rfl⟩; exact into x hx)
  have positiveC := F.constant_positive
  let w : ℝ≥0 := min F.window ⟨δ / (2 * F.constant), by positivity⟩
  have positiveW : 0 < w := lt_min F.window_positive (by
    change (0 : ℝ) < δ / (2 * F.constant)
    positivity)
  refine ⟨w, positiveW, min_le_left _ _, ?_⟩
  intro ε positiveε small control x hx
  have close := F.uniform_close ε positiveε (small.trans (min_le_left _ _)) control x
  have smallε : (ε : ℝ) ≤ δ / (2 * F.constant) := by
    have := small.trans (min_le_right _ _)
    exact_mod_cast this
  have bound : F.constant * (ε : ℝ) < δ := by
    calc F.constant * (ε : ℝ) ≤ F.constant * (δ / (2 * F.constant)) :=
          mul_le_mul_of_nonneg_left smallε positiveC.le
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  apply inside
  exact mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, close.trans_lt bound⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
