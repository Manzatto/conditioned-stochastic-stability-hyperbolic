module
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-! Uniform operator bounds for the literal chart normalizations of a
continuous tangent-frame family over a compact smaller patch. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.CompactCenteredFrameBounds
variable {X E P M : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem uniform_bounds (U K : Set X) (compact : IsCompact K) (inside : K ⊆ U)
    (center : M) (b : X → M)
    (chartInside : ∀ x : U, b x ∈ (chartAt E center).source)
    (A : ∀ x : U, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (b x))
    (sections : ∀ v : P, Continuous (fun x : U =>
      (⟨b x, A x v⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x (hx : x ∈ K),
      ‖(ContinuousCenteredFrameCharts.chartFrame center (b x)
        (chartInside ⟨x, inside hx⟩) (A ⟨x, inside hx⟩)).toContinuousLinearMap‖ ≤ B ∧
      ‖(ContinuousCenteredFrameCharts.chartFrame center (b x)
        (chartInside ⟨x, inside hx⟩) (A ⟨x, inside hx⟩)).symm.toContinuousLinearMap‖ ≤ B := by
  let inclusion : K → U := fun x => ⟨x.val, inside x.property⟩
  have ci : Continuous inclusion := continuous_subtype_val.subtype_mk _
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  have cf := ContinuousCenteredFrameCharts.continuous_frame center (fun x : U => b x)
    chartInside A sections
  have cg := ContinuousCenteredFrameCharts.continuous_inverse_frame center (fun x : U => b x)
    chartInside A sections
  obtain ⟨BF, positiveF, boundF⟩ := ((isCompact_univ : IsCompact (univ : Set K)).image
    (cf.comp ci)).isBounded.exists_pos_norm_le
  obtain ⟨BG, positiveG, boundG⟩ := ((isCompact_univ : IsCompact (univ : Set K)).image
    (cg.comp ci)).isBounded.exists_pos_norm_le
  refine ⟨BF + BG + 1, by linarith, fun x hx => ?_⟩
  have first := boundF _ ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  have second := boundG _ ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  exact ⟨first.trans (by linarith), second.trans (by linarith)⟩

end LeanShared.CompactCenteredFrameBounds
