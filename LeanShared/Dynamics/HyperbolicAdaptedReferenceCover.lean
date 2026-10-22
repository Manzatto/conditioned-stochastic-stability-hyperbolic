module
public import LeanShared.Dynamics.HyperbolicAdaptedReferenceFrames

/-! A single reference tolerance works for a finite family of the actual
adapted frame patches, including comparisons to points outside their compact
smaller pieces. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem PatchSystem.relative_reference_radii (system : PatchSystem b)
    (centers : Finset Λ) (K : Λ → Set Λ)
    (compact : ∀ c, IsCompact (K c)) (inside : ∀ c, K c ⊆ system.frameDomain c)
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η > 0, ∀ c ∈ centers, ∀ x (hx : x ∈ K c), ∀ y, dist x y < η →
      ∃ hy : y ∈ system.frameDomain c,
        ‖(ContinuousCenteredFrameCharts.chartFrame c.val x.val (inside c hx).2
            (system.referenceFrame c ⟨x, inside c hx⟩)).symm.toContinuousLinearMap.comp
          (ContinuousCenteredFrameCharts.chartFrame c.val y.val hy.2
            (system.referenceFrame c ⟨y, hy⟩)).toContinuousLinearMap -
              ContinuousLinearMap.id ℝ _‖ < δ := by
  classical
  induction centers using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert c centers absent ih =>
    obtain ⟨η, positiveη, near⟩ := ih
    obtain ⟨ρ, positiveρ, nearC⟩ :=
      system.relative_reference_radius c (K c) (compact c) (inside c) δ positiveδ
    refine ⟨min ρ η, lt_min positiveρ positiveη, ?_⟩
    intro d hd x hx y small
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact nearC x hx y (small.trans_le (min_le_left _ _))
    · exact near d hd x hx y (small.trans_le (min_le_right _ _))

end LeanShared.HyperbolicAdaptedPatchSystem
