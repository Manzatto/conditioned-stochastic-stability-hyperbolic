module
public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.ConstructedOrderedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection
public import ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import LeanShared.Dynamics.PressureTopologicalOrder
public import LeanShared.Dynamics.PressureBlocks
public import Mathlib.Topology.VectorBundle.Riemannian

/-! The fixed-A filtration of HG1: the pressure order of the retained basic sets, the adapted
source with every shifted boundary null for the product reference, and the dominant index. -/

public noncomputable section
open Set Function Bundle MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG1Filtration
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
variable {E X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Y] [BorelSpace Y]
  {T : X ≃ₜ X} (D : SpectralDecomposition (E := E) T) {g : X → ℝ} {A : Set X}
  (h : HG1 D g A)
  (σP : Measure (X × Y)) [IsFiniteMeasure σP] [σP.IsOpenPosMeasure]
  (strict : MapsTo T (closure A) A)

local notation "σ" => σP

structure FiltrationData where
  order : List (Fin D.count)
  cover : ∀ i, i ∈ order ↔ D.core i ⊆ Aᶜ
  source : AdaptedSource T A D.core order.length
  index : source.index = PressureFiltrationSource.reversedVertex order
  selected : Fin order.length
  selected_dominant : source.index selected = h.dominant
  shifted_boundary : ∀ N j, 0 < j → j ≤ order.length →
    σ (frontier (levels T A D.core order.length N source j ×ˢ (univ : Set Y))) = 0

@[expose] def filtration : FiltrationData D h σP := Classical.choice (by
  classical
  let retained := Finset.univ.filter (fun i => D.core i ⊆ Aᶜ)
  let order := PressureTopologicalOrder.blockOrder D.edge
    (fun i => (D.pressure g i).toReal)
    (PressureTopologicalOrder.wellFounded_of_acyclic D.edge h.no_cycles)
    (PressureBlocks.blocks D.edge (fun i => (D.pressure g i).toReal) retained)
  obtain ⟨coverR, nodup, ordered⟩ := PressureTopologicalOrder.acyclic_pressureBlocks_order_spec
    D.edge (fun i => (D.pressure g i).toReal) h.no_cycles retained
  have cover (i : Fin D.count) : i ∈ order ↔ D.core i ⊆ Aᶜ := by
    simpa only [retained, Finset.mem_filter, Finset.mem_univ, true_and] using coverR i
  have member : h.dominant ∈ order := (cover _).mpr h.dominant_live
  have positive : 0 < order.length := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
  obtain ⟨source, index, boundary, _extra⟩ := ConstructedOrderedFiltration.exists_ordered_product_null_source
    D h.axiomA.periodic_dense A h.absorbing_open strict order positive nodup cover ordered σ
  obtain ⟨selected, same⟩ : ∃ i : Fin order.length,
      PressureFiltrationSource.reversedVertex order i = h.dominant := by
    simpa only [List.nil_append] using
      PressurePrefixSelection.exists_reversed_prefix_index ([] : List (Fin D.count)) order h.dominant member
  refine ⟨{
    order := order
    cover := cover
    source := source
    index := index
    selected := selected
    selected_dominant := ?_
    shifted_boundary := boundary }⟩
  · rw [index]
    exact same)

end ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG1Filtration
