module

public import LeanShared.Analysis.CompactTwoNormDecomposition
public import LeanShared.Analysis.FittingContour
public import LeanShared.Analysis.ShiftedContour

/-! Actual Riesz contour ranges are precisely the finite-dimensional stable
generalized spectral kernels outside the strong growth disk. -/

public section
open ContinuousLinearMap Submodule Metric Set
namespace LeanShared.CompactTwoNormRieszRange
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The actual contour projector around an outer spectral value has range
exactly its stabilized generalized kernel, which is finite dimensional.
All projection, decomposition and pole facts are derived from the estimates. -/
theorem exists_contours (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    ∃ (n : ℕ) (r : ℝ), 0 < r ∧
      FiniteDimensional ℂ ((T - z • 1) ^ n).ker ∧
      (∀ m : ℕ, ((T - z • 1) ^ (n + m)).ker = ((T - z • 1) ^ n).ker) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r →
        sphere z ρ ⊆ resolventSet ℂ T ∧
        (RieszContourIdempotent.projector T z ρ).range = ((T - z • 1) ^ n).ker := by
  let S := T - z • (1 : E →L[ℂ] E)
  obtain ⟨n, finite, compl, kernels, ranges⟩ :=
    CompactTwoNormDecomposition.exists_decomposition T i hi α R C D hα hR hC hD estimate z hz
  obtain ⟨r, hr, hcontours⟩ := FittingContour.exists_contours S n compl (kernels 1) (ranges 1)
  refine ⟨n, r, hr, finite, kernels, fun ρ hρ hsmall => ?_⟩
  have resS := (hcontours ρ hρ hsmall).1
  have resT : sphere z ρ ⊆ resolventSet ℂ T := by
    intro w hw
    have hs := resS (show w - z ∈ sphere (0 : ℂ) ρ by
      simpa only [mem_sphere, dist_eq_norm, sub_zero] using hw)
    change IsUnit (algebraMap ℂ (E →L[ℂ] E) (w - z) - S) at hs
    have shift : algebraMap ℂ (E →L[ℂ] E) (w - z) - S =
        algebraMap ℂ (E →L[ℂ] E) w - T := by
      dsimp only [S]
      simp only [Algebra.algebraMap_eq_smul_one, sub_smul]
      abel
    rw [shift] at hs
    exact hs
  refine ⟨resT, ?_⟩
  have projector : RieszContourIdempotent.projector T z ρ =
      (S ^ n).ker.projectionL (S ^ n).range compl := by
    rw [← ShiftedContour.formula T z ρ]
    exact (hcontours ρ hρ hsmall).2
  rw [projector]
  exact Submodule.range_projectionL compl

end LeanShared.CompactTwoNormRieszRange
