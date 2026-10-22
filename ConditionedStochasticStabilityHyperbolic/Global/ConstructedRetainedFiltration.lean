module
public import ConditionedStochasticStabilityHyperbolic.Global.ConstructedOrderedFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2GreedyFacts

/-! The prescribed HG2 greedy order has a proved fixed-absorber filtration.
Every shifted positive product boundary is null for the original reference. -/
public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.ConstructedRetainedFiltration
open LeanShared ShiftedFiltrationGeometry PressureFiltrationSource Paper.ActualHG2BasinGeometry
variable {E M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace (M × Y)] [BorelSpace (M × Y)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)
  (g : M → ℝ) (A : Set M) (h : Paper.HG2 D g A)
attribute [local instance] Classical.propDecidable

theorem exists_source
    (finitePressure : ∀ i : PaperHG2GreedySelection.Retained D A,
      D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥)
    (strict : MapsTo T (closure A) A) (μ : Measure (M × Y)) [IsFiniteMeasure μ] :
    ∃ S : AdaptedSource T A (retainedCore D A) (greedy D g A h finitePressure).order.length,
      S.index = reversedVertex (greedy D g A h finitePressure).order ∧
      (∀ N j, 0 < j → j ≤ (greedy D g A h finitePressure).order.length →
        μ (frontier (levels T A (retainedCore D A)
          (greedy D g A h finitePressure).order.length N S j ×ˢ (univ : Set Y))) = 0) ∧
      ∀ N (i : Fin (greedy D g A h finitePressure).order.length),
        μ ((closure (filtrationLayer (levels T A (retainedCore D A)
          (greedy D g A h finitePressure).order.length N S) i.val) \
          filtrationLayer (levels T A (retainedCore D A)
            (greedy D g A h finitePressure).order.length N S) i.val) ×ˢ (univ : Set Y)) = 0 := by
  let G := greedy D g A h finitePressure
  let L := G.order.map Subtype.val
  have length : L.length = G.order.length := by simp only [L, List.length_map]
  have positive : 0 < L.length := length.symm ▸ order_positive D g A h finitePressure
  have nodup : L.Nodup := G.nodup.map Subtype.val_injective
  have cover (j : Fin D.count) : j ∈ L ↔ D.core j ⊆ Aᶜ := by
    constructor
    · intro member
      obtain ⟨i, _, same⟩ := List.mem_map.mp member
      exact same ▸ i.property
    · intro live
      exact List.mem_map.mpr ⟨⟨j, live⟩, G.cover _, rfl⟩
  have ordered (i j : Fin L.length) (edge : D.edge (L.get i) (L.get j)) : i < j := by
    let i' : Fin G.order.length := ⟨i.val, length ▸ i.isLt⟩
    let j' : Fin G.order.length := ⟨j.val, length ▸ j.isLt⟩
    apply G.topological i' j'
    simpa only [L, List.get_eq_getElem, List.getElem_map,
      PaperHG2GreedySelection.edge, i', j'] using edge
  obtain ⟨original, index⟩ := ConstructedOrderedFiltration.exists_ordered_source_of_periodic_density
    D h.axiomA.periodic_dense A h.absorbing_open strict L positive nodup cover ordered
  let S : AdaptedSource T A (retainedCore D A) G.order.length := {
    levels := original.levels
    index := reversedVertex G.order
    zero := original.zero
    monotone := original.monotone
    absorbing_forward := original.absorbing_forward
    compact_positive := fun j hj bound => original.compact_positive j hj (length.symm ▸ bound)
    adapted_positive := fun j hj bound => original.adapted_positive j hj (length.symm ▸ bound)
    terminal := length ▸ original.terminal
    literal_core := fun i => by
      have core := original.literal_core ⟨i.val, length.symm ▸ i.isLt⟩
      rw [index] at core
      simpa only [reversedVertex, L, List.length_map, List.get_eq_getElem,
        List.getElem_map, retainedCore] using core }
  obtain ⟨repaired, same, boundary⟩ := AllShiftNullBoundaryFiltration.exists_product_null_replacement
    T A (retainedCore D A) G.order.length S μ
  refine ⟨repaired, same, boundary, ?_⟩
  intro N i
  have ib : i.val < G.order.length := i.isLt
  have marginal (j : ℕ) (hj : 0 < j) (bound : j ≤ G.order.length) :
      (μ.map Prod.fst) (frontier (levels T A (retainedCore D A) G.order.length N repaired j)) = 0 := by
    rw [Measure.map_apply continuous_fst.measurable isClosed_frontier.measurableSet]
    have ready := boundary N j hj bound
    rw [frontier_prod_univ_eq] at ready
    simpa only [prod_univ] using ready
  have extra := AllShiftNullBoundaryFiltration.closed_layer_extra_zero T A h.absorbing_open
    (retainedCore D A) G.order.length N repaired (μ.map Prod.fst) marginal i
  have lower : MeasurableSet (levels T A (retainedCore D A) G.order.length N repaired i.val) := by
    by_cases first : i.val = 0
    · rw [first, levels_zero]
      exact h.absorbing_open.measurableSet
    · exact (levels_positive_compact T A (retainedCore D A) G.order.length N repaired
        i.val (Nat.pos_of_ne_zero first) (by omega)).measurableSet
  have stratum : MeasurableSet (filtrationLayer
      (levels T A (retainedCore D A) G.order.length N repaired) i.val) :=
    (levels_positive_compact T A (retainedCore D A) G.order.length N repaired
      (i.val+1) (by omega) (by omega)).measurableSet.diff lower
  rw [Measure.map_apply continuous_fst.measurable
    (isClosed_closure.measurableSet.diff stratum)] at extra
  simpa only [prod_univ] using extra

end ConditionedStochasticStabilityHyperbolic.Global.ConstructedRetainedFiltration
