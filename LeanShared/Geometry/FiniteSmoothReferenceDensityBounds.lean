module
public import LeanShared.Geometry.FiniteSmoothReferenceDensityRegularity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Quantitative local controls for the actual smooth reference densities.
Both constants are constructed by finite-dimensional compactness; a density
or reciprocal Lipschitz estimate is not supplied as a source field. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set IsManifold
open scoped Manifold ContDiff

theorem Data.localDensity_lipschitzOn_compact
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K : Set E) (compact : IsCompact K) (convex : Convex ℝ K) (inside : K ⊆ c.target) :
    ∃ A B, LipschitzOnWith A (d.localDensity c) K ∧
      LipschitzOnWith B (fun y => (d.localDensity c y)⁻¹) K := by
  obtain ⟨A,first⟩ := ((d.localDensity_contDiffOn c hc).mono inside).exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) convex compact
  obtain ⟨B,last⟩ := ((d.localDensity_inverse_contDiffOn c hc).mono inside).exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) convex compact
  exact ⟨A,B,first,last⟩

end LeanShared.FiniteSmoothReferenceCharts
