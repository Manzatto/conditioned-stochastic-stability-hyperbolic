module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies

/-! Numerical and actual-pressure facts for the computed HG2 prefixes. -/
public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
open PaperHG2GreedySelection PressureFiltrationSource DerivedHG2Basins AssembleShiftedPrefixFamilies
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M}
attribute [local instance] Classical.propDecidable

omit [BorelSpace M] in
theorem order_positive (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥) :
    0 < (greedy D0 g A h finitePressure).order.length := by
  have member := (greedy D0 g A h finitePressure).cover ⟨h.dominant, h.dominant_live⟩
  by_contra hn
  have zero := Nat.eq_zero_of_not_pos hn
  have empty := List.length_eq_zero_iff.mp zero
  simp only [empty, List.not_mem_nil] at member

omit [BorelSpace M] in
theorem family_number_positive (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥) :
    0 < (greedy D0 g A h finitePressure).number :=
  (greedy D0 g A h finitePressure).number_positive (retained_nonempty D0 g A h)

omit [BorelSpace M] in
theorem adapted_pressure_gap (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ)
    (A : Set M) (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥)
    (D : AdaptedSource T A (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length)
    (index_eq : D.index = reversedVertex (greedy D0 g A h finitePressure).order)
    (s : Fin (greedy D0 g A h finitePressure).number)
    (i : Fin (greedy D0 g A h finitePressure).order.length)
    (hi : i.val < ((greedy D0 g A h finitePressure).terminal s).val + 1)
    (different : i ≠ selectedIndex _ _ (greedy D0 g A h finitePressure).terminal
      (greedy D0 g A h finitePressure).selectedRoot s) :
    pressure D0 g A (D.index i) < pressure D0 g A (D.index
      (selectedIndex _ _ (greedy D0 g A h finitePressure).terminal
        (greedy D0 g A h finitePressure).selectedRoot s)) := by
  have neq : (⟨i.val, hi⟩ : Fin (((greedy D0 g A h finitePressure).terminal s).val + 1)) ≠
      (greedy D0 g A h finitePressure).selectedRoot s := by
    intro equal
    apply different
    apply Fin.ext
    have values := congrArg Fin.val equal
    exact values
  have gap := (greedy D0 g A h finitePressure).selected_pressure_gap s ⟨i.val, hi⟩ neq
  simpa only [index_eq, originalIndex, selectedIndex] using gap
end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
