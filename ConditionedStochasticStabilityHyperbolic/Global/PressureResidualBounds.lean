module

public import LeanShared.Dynamics.PressureBlocks

/-!
# Actual selected-root pressure bounds on each remaining prefix

The greedy predecessor-block trace supplies the remaining vertices after any
number of selections and the next selected root's maximal pressure. HG2
pairwise distinct pressures turn this into the strict subordinate separation
consumed by finite spectral confinement; no pressure-gap conclusion is input.
-/

@[expose] public section
open Set Relation Finset
namespace ConditionedStochasticStabilityHyperbolic.Global.PressureResidualBounds
open LeanShared.PressureBlocks
variable {I : Type*} [DecidableEq I] {edge : I → I → Prop} {pressure : I → ℝ}
  {R : Finset I} {L : List (Block I)}

/-- Every suffix of the actual greedy block list is itself a selection
trace on a derived residual subset of the original vertices. -/
theorem exists_residual_trace (h : SelectionTrace edge pressure R L) (n : ℕ) :
    ∃ R' : Finset I, R' ⊆ R ∧ SelectionTrace edge pressure R' (L.drop n) := by
  classical
  induction n generalizing R L with
  | zero => exact ⟨R, Finset.Subset.rfl, by simpa using h⟩
  | succ n ih =>
    cases h with
    | nil => exact ⟨∅, Finset.Subset.rfl, by simpa using SelectionTrace.nil (edge := edge) (pressure := pressure)⟩
    | cons R q hq hp tail ht =>
      obtain ⟨R', hsub, htrace⟩ := ih ht
      exact ⟨R', hsub.trans sdiff_subset, by simpa using htrace⟩

/-- Each head root is chosen by the algorithm at maximal pressure among
ALL remaining vertices, including subsequent blocks. -/
theorem head_root_maximal {b : Block I} {tail : List (Block I)}
    (h : SelectionTrace edge pressure R (b :: tail)) :
    b.root ∈ R ∧ ∀ v ∈ R, pressure v ≤ pressure b.root := by
  cases h with
  | cons _ _ hq hp _ _ => exact ⟨hq, hp⟩

/-- Pairwise pressure distinctness only on retained vertices gives strict
pressure slack for every subordinate remaining vertex. -/
theorem pressure_lt_selected_root {b : Block I} {tail : List (Block I)}
    (h : SelectionTrace edge pressure R (b :: tail))
    (hdistinct : Set.InjOn pressure (R : Set I)) (v : I) (hv : v ∈ R)
    (hne : v ≠ b.root) : pressure v < pressure b.root := by
  obtain ⟨hroot, hmax⟩ := head_root_maximal h
  apply lt_of_le_of_ne (hmax v hv)
  intro he
  exact hne (hdistinct hv hroot he)

/-- The exact residual vertex set is covered by precisely the remaining
selected blocks; this identifies the vertices of each retained prefix. -/
theorem residual_members_iff (h : SelectionTrace edge pressure R L) (n : ℕ) :
    ∃ R' : Finset I, R' ⊆ R ∧ (∀ v, v ∈ R' ↔ ∃ b ∈ L.drop n, v ∈ b.members) ∧
      SelectionTrace edge pressure R' (L.drop n) := by
  obtain ⟨R', hsub, ht⟩ := exists_residual_trace h n
  exact ⟨R', hsub, fun v => (ht.covers v).symm, ht⟩

end ConditionedStochasticStabilityHyperbolic.Global.PressureResidualBounds
