module
public import LeanShared.Geometry.FiniteSmoothReferenceJacobian

/-! Every fixed C1 diffeomorphism has bounded reference pushforward on a
compact manifold. The bound is derived from the actual Jacobian density. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Manifold ContDiff ENNReal

theorem Data.exists_map_domination
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (H : M ≃ₜ M) (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (d.measure μ).map H ≤ C • d.measure μ := by
  obtain ⟨continuous, _, formula⟩ := d.jacobian_continuous_positive_map μ H forward inverse
  obtain ⟨B, bound⟩ := isCompact_univ.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, ?_⟩
  rw [formula, ← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using bound x (mem_univ x))))

end LeanShared.FiniteSmoothReferenceCharts
