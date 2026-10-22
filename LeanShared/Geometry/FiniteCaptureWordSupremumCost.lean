module
public import LeanShared.Geometry.FiniteCaptureWordInflation
public import LeanShared.Analysis.PressureCoverRefinement

/-! The actual finite capture partition controls the SUM of labelwise
supremum costs on one tracked orbit tube. Constants and tube radius are
chosen before every word length; no number-of-label-words factor occurs. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanShared.FiniteSmoothCapturePartition
open PressureCoverRefinement
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype I]
  {K : Set M} {v : I → Set M}

theorem Data.exists_word_cost_radius (d : Data (E := E) K v)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ, ∀ center : Fin n → M,
      (∀ j, center j ∈ d.capture) →
      ∀ L cell : Set M, ∀ points : Fin n → M → M, ∀ A : M → ℝ, ∀ B : ℝ,
      0 ≤ B →
      (∀ x ∈ L ∩ cell, ∀ j, dist (center j) (points j x) < ρ) →
      (∀ x ∈ L ∩ cell, A x ≤ B) →
      (∑ labels : Fin n → I, domainCoefficient L cell
        (fun x => wordCutoff d (fun j => points j x) labels * A x)) ≤
      B * Real.exp (δ * n) := by
  obtain ⟨η,ρ,positiveη,positiveρ,_,near,sumBudget⟩ := d.exists_inflated_word_budget positive
  refine ⟨ρ,positiveρ,fun n center capture L cell points A B nonnegativeB tracking bound => ?_⟩
  have each (labels : Fin n → I) : domainCoefficient L cell
      (fun x => wordCutoff d (fun j => points j x) labels * A x) ≤
        inflatedWordCutoff d η center labels * B := by
    have nonnegativeInflated : 0 ≤ inflatedWordCutoff d η center labels :=
      Finset.prod_nonneg (fun j _ => add_nonneg (d.bounds (labels j) (center j)).1 positiveη.le)
    apply csSup_le (s := {0} ∪
      (fun x => wordCutoff d (fun j => points j x) labels * A x) '' (L ∩ cell))
      ⟨0,Or.inl (mem_singleton 0)⟩
    rintro z (zero | ⟨x,hx,rfl⟩)
    · rcases mem_singleton_iff.mp zero with rfl
      exact mul_nonneg nonnegativeInflated nonnegativeB
    · have cutoffBound := wordCutoff_le_inflated d η center (fun j => points j x)
        (fun j i => near (center j) (points j x) (tracking x hx j) i) labels
      exact (mul_le_mul_of_nonneg_left (bound x hx)
        (wordCutoff_nonneg d (fun j => points j x) labels)).trans
          (mul_le_mul_of_nonneg_right cutoffBound nonnegativeB)
  calc
    _ ≤ ∑ labels : Fin n → I, inflatedWordCutoff d η center labels * B :=
      Finset.sum_le_sum (fun labels _ => each labels)
    _ = (∑ labels : Fin n → I, inflatedWordCutoff d η center labels) * B :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ Real.exp (δ * n) * B := mul_le_mul_of_nonneg_right (sumBudget n center capture) nonnegativeB
    _ = B * Real.exp (δ * n) := mul_comm _ _

end LeanShared.FiniteSmoothCapturePartition
