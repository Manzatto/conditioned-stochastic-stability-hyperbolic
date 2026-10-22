module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Full support after restricting to the closure of an open region

Every nonempty ambient open set has positive reference volume. Restricting
that volume to the closure of an open live region gives precisely that closed
region as support, including its boundary. No boundary-volume assumption or
regularity of the boundary is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace LeanShared

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem support_restrict_closure_open (μ : Measure X) [μ.IsOpenPosMeasure]
    {V : Set X} (hV : IsOpen V) : (μ.restrict (closure V)).support = closure V := by
  apply Subset.antisymm
  · intro x hx
    simpa only [closure_closure] using (Measure.support_restrict_subset hx).1
  · apply closure_minimal _ Measure.isClosed_support
    intro x hx
    rw [Measure.support_eq_forall_isOpen]
    intro N hxN hN
    rw [Measure.restrict_apply hN.measurableSet]
    have hp : 0 < μ (N ∩ V) := (hN.inter hV).measure_pos μ ⟨x, hxN, hx⟩
    apply hp.trans_le
    apply measure_mono
    exact fun y hy => ⟨hy.1, subset_closure hy.2⟩

/-- Interior points remain supported after restriction to any live set.
The whole closed live set need not be the support. -/
theorem interior_subset_support_restrict (μ : Measure X) [μ.IsOpenPosMeasure]
    (K : Set X) : interior K ⊆ (μ.restrict K).support := by
  intro x hx
  rw [Measure.support_eq_forall_isOpen]
  intro N hxN hN
  rw [Measure.restrict_apply hN.measurableSet]
  exact ((hN.inter isOpen_interior).measure_pos μ ⟨x, hxN, hx⟩).trans_le
    (measure_mono (inter_subset_inter_right N interior_subset))

/-- A core in the interior of the live region has reference support even
when the live boundary has additional null components. -/
theorem subset_support_restrict_of_subset_interior (μ : Measure X)
    [μ.IsOpenPosMeasure] {Λ K : Set X} (hΛ : Λ ⊆ interior K) :
    Λ ⊆ (μ.restrict K).support :=
  hΛ.trans (interior_subset_support_restrict μ K)

end LeanShared
