module

public import LeanShared.Geometry.SmoothWeightCutoff

/-! A smooth cutoff only needs nonnegativity on its supporting open region.
A regular extension of a positive live weight may have arbitrary sign away
from that region; truncating it by max(0,.) is unnecessary. -/

@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.SmoothWeightCutoff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_weight_cutoff_of_local_nonnegative (S V : Set M)
    (hS : IsCompact S) (hV : IsOpen V) (hSV : S ⊆ V)
    (w : M → ℝ) (hw : Continuous w) (hw0 : ∀ x ∈ V, 0 ≤ w x) :
    ∃ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ tsupport ζ ⊆ V ∧
      Continuous (ζ * w) ∧ (∀ x, 0 ≤ (ζ * w) x) ∧
      tsupport (ζ * w) ⊆ V ∧ EqOn (ζ * w) w S := by
  obtain ⟨ζ, smooth, bound, support, one⟩ := exists_cutoff (E := E) S V hS hV hSV
  refine ⟨ζ, smooth, bound, support, smooth.continuous.mul hw, ?_,
    tsupport_mul_subset_left.trans support, ?_⟩
  · intro x
    by_cases hx : ζ x = 0
    · simp [Pi.mul_apply, hx]
    · exact mul_nonneg (bound x).1 (hw0 x (support (subset_tsupport ζ hx)))
  · intro x hx
    change ζ x * w x = w x
    rw [one x hx, one_mul]

end LeanShared.SmoothWeightCutoff
