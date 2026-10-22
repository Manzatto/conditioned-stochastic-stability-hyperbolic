module
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import LeanShared.Analysis.CompactRelativeFrameComparison

/-! Uniform comparison of the actual tangent-frame normalizations in a fixed
manifold chart. The compact set may be a smaller hyperbolic-core patch. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.CompactCenteredFrameComparison
variable {X E P M : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem exists_radius (U K : Set X) (openU : IsOpen U) (compact : IsCompact K)
    (inside : K ⊆ U) (center : M) (b : X → M)
    (chartInside : ∀ x : U, b x ∈ (chartAt E center).source)
    (A : ∀ x : U, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (b x))
    (sections : ∀ v : P, Continuous (fun x : U =>
      (⟨b x, A x v⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η > 0, ∀ x (hx : x ∈ K), ∀ y, dist x y < η →
      ∃ hy : y ∈ U,
        ‖(ContinuousCenteredFrameCharts.chartFrame center (b x)
          (chartInside ⟨x, inside hx⟩) (A ⟨x, inside hx⟩)).symm.toContinuousLinearMap.comp
          (ContinuousCenteredFrameCharts.chartFrame center (b y)
            (chartInside ⟨y, hy⟩) (A ⟨y, hy⟩)).toContinuousLinearMap -
              ContinuousLinearMap.id ℝ P‖ < δ := by
  exact CompactRelativeFrameComparison.exists_radius U K openU compact inside
    (fun x => ContinuousCenteredFrameCharts.chartFrame center (b x) (chartInside x) (A x))
    (ContinuousCenteredFrameCharts.continuous_frame center (fun x : U => b x)
      chartInside A sections) δ positiveδ

end LeanShared.CompactCenteredFrameComparison
