module

public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry

/-!
# Null closed-layer discrepancies from positive smooth boundaries

The classical smooth-boundary null theorem and the diffeomorphism's null-set
preimage theorem apply only to positive levels. Their checked consequences
survive a common preimage shift and supply the closed-layer/actual-stratum
null discrepancy. No nullity of the absorbing boundary is required.
-/

@[expose] public noncomputable section
open MeasureTheory Set Function
namespace ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- Homeomorphism preimages commute with frontiers at every finite iterate. -/
theorem preimage_iterate_frontier (T : X ≃ₜ X) (K : Set X) (N : ℕ) :
    (T : X → X)^[N] ⁻¹' frontier K = frontier ((T : X → X)^[N] ⁻¹' K) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change T ⁻¹' ((T : X → X)^[N] ⁻¹' frontier K) =
        frontier (T ⁻¹' ((T : X → X)^[N] ⁻¹' K))
      rw [ih, T.preimage_frontier]

/-- The cited diffeomorphism null-preimage statement gives all finite shifts. -/
theorem measure_preimage_iterate_zero (T : X ≃ₜ X) (σ : Measure X)
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (K : Set X) (hK : σ K = 0) (N : ℕ) :
    σ ((T : X → X)^[N] ⁻¹' K) = 0 := by
  induction N with
  | zero => exact hK
  | succ N ih =>
      change σ (T ⁻¹' ((T : X → X)^[N] ⁻¹' K)) = 0
      exact hpre _ ih

/-- Every positive shifted smooth level retains its reference-null frontier. -/
theorem shifted_positive_frontier_zero
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (σ : Measure X)
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0)
    (i : ℕ) (hi : 0 < i) (hiℓ : i ≤ ℓ) :
    σ (frontier (levels T A Λ ℓ N D i)) = 0 := by
  rw [levels, shiftedFiltration_pos T N A D.levels hi, ← preimage_iterate_frontier]
  exact measure_preimage_iterate_zero T σ hpre _ (hnull i hi hiℓ) N

/-- Exact null discrepancy for each closed analytic layer versus literal
stratum; the first layer is equal rather than merely equal almost everywhere. -/
theorem closed_layer_extra_zero
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (σ : Measure X)
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0)
    (i : Fin ℓ) :
    σ (closure (filtrationLayer (levels T A Λ ℓ N D) i.val) \
      filtrationLayer (levels T A Λ ℓ N D) i.val) = 0 := by
  by_cases hi : i.val = 0
  · have hclosed : IsClosed (filtrationLayer (levels T A Λ ℓ N D) i.val) := by
      rw [hi, filtrationLayer, zero_add, levels_zero]
      exact absorbing_stratum_closed _ A
        (levels_positive_compact T A Λ ℓ N D 1 (by omega) (by omega)).isClosed hA
    rw [hclosed.closure_eq, sdiff_self, measure_empty]
  · apply closed_stratum_extra_measure_zero
      σ (levels T A Λ ℓ N D (i.val + 1)) (levels T A Λ ℓ N D i.val)
      (levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)).isClosed
      (levels_positive_compact T A Λ ℓ N D i.val (Nat.pos_of_ne_zero hi) (by omega)).isClosed
    exact shifted_positive_frontier_zero T A Λ ℓ N D σ hpre hnull i.val
      (Nat.pos_of_ne_zero hi) (by omega)

end ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry
