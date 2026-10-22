module
public import ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixEncoding
public import ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import LeanShared.Dynamics.TrappingBoundarySeparation

/-! Actual HG2 determines all greedy prefixes and their basin assignment.
Strict trapping is a separate, explicit hypothesis. Only existence of an
adapted filtration for this computed compatible order remains classical. -/
public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
open PaperHG2GreedySelection PressureFiltrationSource DerivedHG2Basins
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M}

attribute [local instance] Classical.propDecidable

abbrev retainedCore (D : SpectralDecomposition (E := E) T) (A : Set M)
    (i : Retained D A) : Set M := D.core i.val

def greedy (D : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D g A)
    (finitePressure : ∀ i : Retained D A, D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥) :=
  GreedyPrefixGeometry.ofGraph (edge D A) (pressure D g A)
    (acyclic D g A h) (pressure_injective D g A h finitePressure)

omit [BorelSpace M] in
theorem retained_nonempty (D : SpectralDecomposition (E := E) T) (g : M → ℝ)
    (A : Set M) (h : HG2 D g A) : Nonempty (Retained D A) :=
  ⟨⟨h.dominant, h.dominant_live⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem retained_invariant (D : SpectralDecomposition (E := E) T) (A : Set M)
    (i : Retained D A) : T '' retainedCore D A i = retainedCore D A i :=
  (D.basic i.val).hyperbolic.invariant

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem retained_core_nonempty (D : SpectralDecomposition (E := E) T) (A : Set M)
    (i : Retained D A) : (retainedCore D A i).Nonempty := (D.basic i.val).nonempty

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem retained_separation (D : SpectralDecomposition (E := E) T) (A : Set M)
    (strict : MapsTo T (closure A) A) (i : Retained D A) :
    retainedCore D A i ⊆ interior Aᶜ := by
  apply invariant_subset_interior_live_of_strict_trapping T A (retainedCore D A i)
  · rintro _ ⟨x, hx, rfl⟩
    exact strict hx
  · exact (retained_invariant D A i).le
  · exact disjoint_left.mpr (fun _ hx ha => i.property hx ha)

omit [BorelSpace M] in
theorem adapted_assignment (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ)
    (A : Set M) (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥)
    (D : AdaptedSource T A (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length)
    (index_eq : D.index = reversedVertex (greedy D0 g A h finitePressure).order)
    (j : Fin (greedy D0 g A h finitePressure).order.length) :
    ∃ s : Fin (greedy D0 g A h finitePressure).number,
    ∃ i : Fin (((greedy D0 g A h finitePressure).terminal s).val + 1),
      retainedCore D0 A (D.index j) = retainedCore D0 A (D.index (originalIndex i)) ∧
      ReflTransGen (fun a b => D0.edge (D.index (originalIndex a)).val
        (D.index (originalIndex b)).val) i ((greedy D0 g A h finitePressure).selectedRoot s) := by
  obtain ⟨s, i, same, path⟩ := (greedy D0 g A h finitePressure).selected_assignment j
  refine ⟨s, i, congrArg (fun q => retainedCore D0 A (D.index q)) same, ?_⟩
  simpa only [index_eq, PaperHG2GreedySelection.edge] using path

omit [BorelSpace M] in
theorem adapted_transitive (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ)
    (A : Set M) (h : HG2 D0 g A) (ℓ : ℕ)
    (D : AdaptedSource T A (retainedCore D0 A) ℓ) (i : Fin ℓ) :
    ControlledPlaqueClosure.forwardTransitiveOn T (retainedCore D0 A (D.index i)) :=
  (h.retained_mixing (D.index i).val (D.index i).property).forwardTransitiveOn

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem adapted_connections (D0 : SpectralDecomposition (E := E) T) (A : Set M) (ℓ : ℕ)
    (D : AdaptedSource T A (retainedCore D0 A) ℓ) (i j : Fin ℓ)
    (e : D0.edge (D.index i).val (D.index j).val) : ∃ z : M,
      (∀ a : ℝ, 0 < a → ∃ n : ℕ, ∃ y ∈ retainedCore D0 A (D.index j),
        dist ((T : M → M)^[n + 1] z) y < a) ∧
      (∀ a : ℝ, 0 < a → ∃ n : ℕ, ∃ y ∈ retainedCore D0 A (D.index i),
        dist ((T.symm : M → M)^[n] z) y < a) :=
  PaperStableBasin.metric_approaches_of_heteroclinicRelation T D0.core
    (D.index i).val (D.index j).val e
end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
