module

public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! A single replacement of an adapted filtration has null boundaries at
every deterministic backward shift. The reference need not preserve null
sets under the dynamics: the construction applies boundary replacement to
the countable sum of its forward pushforwards. The absorbing base, indexing
and literal isolated cores are retained. -/

public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.AllShiftNullBoundaryFiltration
open LeanShared ShiftedFiltrationGeometry

variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Nullity can be arranged simultaneously for all shifted positive levels,
without assuming that the homeomorphism preserves reference-null sets. -/
theorem exists_replacement (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (original : AdaptedSource T A Λ ℓ) (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ repaired : AdaptedSource T A Λ ℓ,
      repaired.index = original.index ∧
      ∀ N j, 0 < j → j ≤ ℓ →
        μ (frontier (levels T A Λ ℓ N repaired j)) = 0 := by
  let references (N : ℕ) : Measure X := μ.map ((T : X → X)^[N])
  have (N : ℕ) : IsFiniteMeasure (references N) := by
    dsimp only [references]
    infer_instance
  obtain ⟨repaired, index, boundary⟩ :=
    NullBoundaryAdaptedFiltration.exists_replacement T A Λ ℓ original (Measure.sum references)
  refine ⟨repaired, index, ?_⟩
  intro N j positive bound
  have null : references N (frontier (repaired.levels j)) = 0 :=
    (Measure.sum_apply_eq_zero.mp (boundary j positive bound)) N
  dsimp only [references] at null
  rw [Measure.map_apply (T.continuous.iterate N).measurable
    isClosed_frontier.measurableSet] at null
  rw [levels, shiftedFiltration_pos T N A repaired.levels positive,
    ← ShiftedBoundaryGeometry.preimage_iterate_frontier]
  exact null

omit [CompactSpace X] [BorelSpace X] in
/-- Actual shifted boundary nullity alone supplies the closed-layer/stratum
identity almost everywhere. No transport-of-null-sets premise is needed. -/
theorem closed_layer_extra_zero (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A)
    (Λ : I → Set X) (ℓ N : ℕ) (D : AdaptedSource T A Λ ℓ) (μ : Measure X)
    (boundary : ∀ j, 0 < j → j ≤ ℓ →
      μ (frontier (levels T A Λ ℓ N D j)) = 0) (i : Fin ℓ) :
    μ (closure (filtrationLayer (levels T A Λ ℓ N D) i.val) \
      filtrationLayer (levels T A Λ ℓ N D) i.val) = 0 := by
  by_cases first : i.val = 0
  · have closed : IsClosed (filtrationLayer (levels T A Λ ℓ N D) i.val) := by
      rw [first, filtrationLayer, zero_add, levels_zero]
      exact FiltrationLayerGeometry.absorbing_stratum_closed _ A
        (levels_positive_compact T A Λ ℓ N D 1 (by omega) (by omega)).isClosed hA
    rw [closed.closure_eq, sdiff_self, measure_empty]
  · apply FiltrationLayerGeometry.closed_stratum_extra_measure_zero
      μ (levels T A Λ ℓ N D (i.val + 1)) (levels T A Λ ℓ N D i.val)
      (levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)).isClosed
      (levels_positive_compact T A Λ ℓ N D i.val (Nat.pos_of_ne_zero first) (by omega)).isClosed
    exact boundary i.val (Nat.pos_of_ne_zero first) (by omega)

/-- The same single replacement works for any finite joint reference on a
product, using its first marginal. Product-measure structure is unnecessary. -/
theorem exists_product_null_replacement {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace (X × Y)] [BorelSpace (X × Y)]
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (original : AdaptedSource T A Λ ℓ) (μ : Measure (X × Y)) [IsFiniteMeasure μ] :
    ∃ repaired : AdaptedSource T A Λ ℓ,
      repaired.index = original.index ∧
      ∀ N j, 0 < j → j ≤ ℓ →
        μ (frontier (levels T A Λ ℓ N repaired j ×ˢ (univ : Set Y))) = 0 := by
  obtain ⟨repaired, index, boundary⟩ := exists_replacement T A Λ ℓ original (μ.map Prod.fst)
  refine ⟨repaired, index, ?_⟩
  intro N j positive bound
  have null := boundary N j positive bound
  rw [Measure.map_apply continuous_fst.measurable isClosed_frontier.measurableSet] at null
  rw [frontier_prod_univ_eq]
  simpa only [prod_univ] using null

end ConditionedStochasticStabilityHyperbolic.Global.AllShiftNullBoundaryFiltration
