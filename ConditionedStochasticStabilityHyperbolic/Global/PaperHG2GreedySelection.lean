module

public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.HG2BasicSetAssignment

/-! # Greedy global selection from the manuscript's actual HG2 data

The finite graph is the literal stable/unstable heteroclinic graph. Its
pressures are the real values of the separated-set pressures, with finiteness
an ordinary thermodynamic input. Neither a graph ordering nor a selected
prefix accessibility conclusion is supplied.
-/
@[expose] public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
open LeanShared HyperbolicBasicSet Paper
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} (D : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)

attribute [local instance] Classical.propDecidable

abbrev Retained := {i : Fin D.count // D.core i ⊆ Aᶜ}

def edge (i j : Retained D A) : Prop := D.edge i.val j.val

def pressure (i : Retained D A) : ℝ := (D.pressure g i.val).toReal

omit [BorelSpace M] in
theorem acyclic (h : HG2 D g A) : ∀ i : Retained D A, ¬TransGen (edge D A) i i := by
  intro i hi
  exact h.no_cycles i.val (hi.lift Subtype.val (fun _ _ he => he))

omit [BorelSpace M] in
theorem pressure_injective (h : HG2 D g A)
    (hfinite : ∀ i : Retained D A, D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥) :
    Function.Injective (pressure D g A) := by
  intro i j hij
  apply Subtype.ext
  apply h.pressures_distinct i.val j.val i.property j.property
  exact (EReal.toReal_eq_toReal (hfinite i).1 (hfinite i).2
    (hfinite j).1 (hfinite j).2).mp hij

omit [MeasurableSpace M] [BorelSpace M] in
theorem actual_pressure_value
    (hfinite : ∀ i : Retained D A, D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥)
    (i : Retained D A) : (pressure D g A i : EReal) = D.pressure g i.val :=
  EReal.coe_toReal (hfinite i).1 (hfinite i).2

omit [BorelSpace M] in
theorem retained_pressure_gap_from_HG1 (h : HG1 D g A)
    (hfinite : ∀ i : Retained D A, D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥)
    (i : Retained D A) (hi : i.val ≠ h.dominant) :
    pressure D g A i < pressure D g A ⟨h.dominant, h.dominant_live⟩ := by
  apply EReal.coe_lt_coe_iff.mp
  rw [actual_pressure_value D g A hfinite i,
    actual_pressure_value D g A hfinite ⟨h.dominant, h.dominant_live⟩]
  exact h.pressure_dominant i.val i.property hi

open PressureBlocks PressureTopologicalOrder PressureFiltrationSource PressurePrefixSelection

omit [BorelSpace M] in
theorem every_retained_basic_has_actual_selected_prefix
    (h : HG2 D g A)
    (hfinite : ∀ i : Retained D A, D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥)
    (v : Retained D A) :
    ∃ n : ℕ, ∃ b : Block (Retained D A), ∃ tail : List (Block (Retained D A)),
      (blocks (edge D A) (pressure D g A) Finset.univ).drop n = b :: tail ∧ v ∈ b.members ∧
      let L := blockOrder (edge D A) (pressure D g A)
        (wellFounded_of_acyclic (edge D A) (acyclic D g A h)) (b :: tail)
      ∃ start root : Fin L.length,
        reversedVertex L start = v ∧ reversedVertex L root = b.root ∧
        (∀ i : Fin L.length, i ≠ root →
          pressure D g A (reversedVertex L i) < pressure D g A b.root) ∧
        ReflTransGen (fun a c : Fin L.length =>
          edge D A (reversedVertex L a) (reversedVertex L c)) start root := by
  classical
  exact HG2BasicSetAssignment.exists_actual_prefix_for_each_retained_basic_set
    (edge D A) (pressure D g A) (acyclic D g A h) (pressure_injective D g A h hfinite) v

end ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
