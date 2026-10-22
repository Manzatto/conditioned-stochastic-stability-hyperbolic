module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Pairwise
public import Mathlib.Logic.Relation
public import Mathlib.Basic.Real.Basic

/-!
# Pressure-selected predecessor blocks of a finite directed relation

At each step choose a maximum-pressure remaining vertex and remove its entire
remaining predecessor block, using actual reflexive-transitive reachability.
The algorithm terminates by decreasing the remaining cardinality. The blocks
partition the initial vertices; every member reaches its selected root, and
no vertex in a later block reaches a vertex in an earlier block.

These block conclusions hold even in the presence of cycles. Acyclicity is
needed for a further within-block topological order (the manuscript's R3),
which is not asserted here. Numerical pressure order alone is never used as
a substitute for reachability.
-/

@[expose] public noncomputable section

open Finset Relation

namespace LeanShared.PressureBlocks

variable {V : Type*}

/-- A selected vertex and the literal predecessor block removed with it. -/
structure Block (V : Type*) where
  root : V
  members : Finset V

/-- Predecessors of `q` which are still in the residual vertex set. -/
def predecessorBlock (edge : V → V → Prop) (R : Finset V) (q : V) : Finset V := by
  classical
  exact R.filter (fun v => ReflTransGen edge v q)

@[simp]
theorem mem_predecessorBlock (edge : V → V → Prop) (R : Finset V) (q v : V) :
    v ∈ predecessorBlock edge R q ↔ v ∈ R ∧ ReflTransGen edge v q := by
  classical
  simp [predecessorBlock]

theorem predecessorBlock_subset (edge : V → V → Prop) (R : Finset V) (q : V) :
    predecessorBlock edge R q ⊆ R := fun v hv => (mem_predecessorBlock edge R q v).mp hv |>.1

theorem root_mem_predecessorBlock (edge : V → V → Prop) (R : Finset V) (q : V) (hq : q ∈ R) :
    q ∈ predecessorBlock edge R q :=
  (mem_predecessorBlock edge R q q).mpr ⟨hq, .refl⟩

/-- Predecessor closure is what prevents backwards cross-block edges. -/
theorem predecessorBlock_closed (edge : V → V → Prop) (R : Finset V) (q x y : V)
    (hx : x ∈ R) (hy : y ∈ predecessorBlock edge R q) (hxy : ReflTransGen edge x y) :
    x ∈ predecessorBlock edge R q :=
  (mem_predecessorBlock edge R q x).mpr
    ⟨hx, hxy.trans ((mem_predecessorBlock edge R q y).mp hy).2⟩

variable [DecidableEq V]

theorem remaining_not_reach_block (edge : V → V → Prop) (R : Finset V) (q x y : V)
    (hx : x ∈ R \ predecessorBlock edge R q) (hy : y ∈ predecessorBlock edge R q) :
    ¬ReflTransGen edge x y := by
  intro hxy
  exact (mem_sdiff.mp hx).2
    (predecessorBlock_closed edge R q x y (mem_sdiff.mp hx).1 hy hxy)

/-- A maximum of a real-valued function on a nonempty finite residual set. -/
def pressureMax (pressure : V → ℝ) (R : Finset V) (hR : R.Nonempty) : V :=
  Classical.choose (R.exists_max_image pressure hR)

omit [DecidableEq V] in
theorem pressureMax_mem (pressure : V → ℝ) (R : Finset V) (hR : R.Nonempty) :
    pressureMax pressure R hR ∈ R :=
  (Classical.choose_spec (R.exists_max_image pressure hR)).1

omit [DecidableEq V] in
theorem pressureMax_spec (pressure : V → ℝ) (R : Finset V) (hR : R.Nonempty)
    (v : V) (hv : v ∈ R) : pressure v ≤ pressure (pressureMax pressure R hR) :=
  (Classical.choose_spec (R.exists_max_image pressure hR)).2 v hv

private theorem remaining_card_lt (edge : V → V → Prop) (pressure : V → ℝ)
    (R : Finset V) (hR : R.Nonempty) :
    (R \ predecessorBlock edge R (pressureMax pressure R hR)).card < R.card := by
  apply card_lt_card
  apply sdiff_ssubset (predecessorBlock_subset edge R _)
  exact ⟨_, root_mem_predecessorBlock edge R _ (pressureMax_mem pressure R hR)⟩

/-- The actual finite greedy predecessor-block algorithm. Ties may be chosen
arbitrarily; reachability determines block membership. -/
def blocks (edge : V → V → Prop) (pressure : V → ℝ) (R : Finset V) : List (Block V) := by
  classical
  exact if hR : R.Nonempty then
    let q := pressureMax pressure R hR
    let B := predecessorBlock edge R q
    ⟨q, B⟩ :: blocks edge pressure (R \ B)
  else []
termination_by R.card
decreasing_by exact remaining_card_lt edge pressure R hR

/-- A raw selection trace records only the algorithm's recursive choices,
not any of its partition, reachability or ordering conclusions. -/
inductive SelectionTrace (edge : V → V → Prop) (pressure : V → ℝ) :
    Finset V → List (Block V) → Prop
  | nil : SelectionTrace edge pressure ∅ []
  | cons (R : Finset V) (q : V) (hq : q ∈ R)
      (hp : ∀ v ∈ R, pressure v ≤ pressure q) (tail : List (Block V))
      (htail : SelectionTrace edge pressure (R \ predecessorBlock edge R q) tail) :
      SelectionTrace edge pressure R (⟨q, predecessorBlock edge R q⟩ :: tail)

/-- The implemented recursion really supplies the recorded choices. -/
theorem blocks_selectionTrace (edge : V → V → Prop) (pressure : V → ℝ) (R : Finset V) :
    SelectionTrace edge pressure R (blocks edge pressure R) := by
  classical
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R.Nonempty
  · rw [blocks, dite_eq_left hR]
    apply SelectionTrace.cons R _ (pressureMax_mem pressure R hR)
      (fun v hv => pressureMax_spec pressure R hR v hv)
    apply ih
    apply sdiff_ssubset (predecessorBlock_subset edge R _)
    exact ⟨_, root_mem_predecessorBlock edge R _ (pressureMax_mem pressure R hR)⟩
  · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    subst R
    rw [blocks, dite_eq_right (Finset.not_nonempty_empty)]
    exact SelectionTrace.nil

namespace SelectionTrace

variable {edge : V → V → Prop} {pressure : V → ℝ} {R : Finset V} {L : List (Block V)}

theorem members_subset (h : SelectionTrace edge pressure R L) (b : Block V) (hb : b ∈ L) :
    b.members ⊆ R := by
  induction h generalizing b with
  | nil => simp at hb
  | cons R q _ _ tail _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact predecessorBlock_subset edge R q
      · exact (ih b hb).trans sdiff_subset

theorem root_mem (h : SelectionTrace edge pressure R L) (b : Block V) (hb : b ∈ L) :
    b.root ∈ b.members := by
  induction h generalizing b with
  | nil => simp at hb
  | cons R q hq _ tail _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact root_mem_predecessorBlock edge R q hq
      · exact ih b hb

/-- Each vertex has a genuine directed path to its own selected root. -/
theorem reaches_root (h : SelectionTrace edge pressure R L) (b : Block V) (hb : b ∈ L)
    (v : V) (hv : v ∈ b.members) : ReflTransGen edge v b.root := by
  induction h generalizing b with
  | nil => simp at hb
  | cons R q _ _ tail _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ((mem_predecessorBlock edge R q v).mp hv).2
      · exact ih b hb hv

theorem pressure_le_root (h : SelectionTrace edge pressure R L) (b : Block V) (hb : b ∈ L)
    (v : V) (hv : v ∈ b.members) : pressure v ≤ pressure b.root := by
  induction h generalizing b with
  | nil => simp at hb
  | cons R q _ hp tail _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hp v ((mem_predecessorBlock edge R q v).mp hv).1
      · exact ih b hb hv

/-- The blocks cover exactly the initial residual vertices. -/
theorem covers (h : SelectionTrace edge pressure R L) (v : V) :
    (∃ b ∈ L, v ∈ b.members) ↔ v ∈ R := by
  constructor
  · rintro ⟨b, hb, hv⟩
    exact h.members_subset b hb hv
  · intro hv
    induction h with
    | nil => simp at hv
    | cons R q _ _ tail _ ih =>
        by_cases hB : v ∈ predecessorBlock edge R q
        · exact ⟨_, List.mem_cons_self, hB⟩
        · obtain ⟨b, hb, hvb⟩ := ih (mem_sdiff.mpr ⟨hv, hB⟩)
          exact ⟨b, List.mem_cons_of_mem _ hb, hvb⟩

/-- Distinct selection steps remove disjoint vertex sets. -/
theorem pairwise_disjoint (h : SelectionTrace edge pressure R L) :
    L.Pairwise (fun b c => Disjoint b.members c.members) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q _ _ tail ht ih =>
      apply List.Pairwise.cons _ ih
      intro b hb
      apply Finset.disjoint_left.mpr
      intro v hvB hvb
      exact (mem_sdiff.mp (ht.members_subset b hb hvb)).2 hvB

/-- Later blocks cannot reach earlier blocks, so in particular every
cross-block edge has the required filtration direction. -/
theorem pairwise_no_backward_reach (h : SelectionTrace edge pressure R L) :
    L.Pairwise (fun b c => ∀ x ∈ c.members, ∀ y ∈ b.members, ¬ReflTransGen edge x y) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q _ _ tail ht ih =>
      apply List.Pairwise.cons _ ih
      intro b hb x hx y hy
      exact remaining_not_reach_block edge R q x y (ht.members_subset b hb hx) hy

theorem pairwise_pressure_nonincreasing (h : SelectionTrace edge pressure R L) :
    L.Pairwise (fun b c => pressure c.root ≤ pressure b.root) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q _ hp tail ht ih =>
      apply List.Pairwise.cons _ ih
      intro b hb
      exact hp b.root (sdiff_subset (ht.members_subset b hb (ht.root_mem b hb)))

/-- Distinct pressures, as in HG2, give strictly decreasing selected-root pressures. -/
theorem pairwise_pressure_strict (h : SelectionTrace edge pressure R L)
    (hp_inj : Function.Injective pressure) :
    L.Pairwise (fun b c => pressure c.root < pressure b.root) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q hq hp tail ht ih =>
      apply List.Pairwise.cons _ ih
      intro b hb
      have hroot := ht.members_subset b hb (ht.root_mem b hb)
      have hne : b.root ≠ q := by
        intro he
        rw [he] at hroot
        exact (mem_sdiff.mp hroot).2 (root_mem_predecessorBlock edge R q hq)
      exact lt_of_le_of_ne (hp b.root (sdiff_subset hroot)) (fun he => hne (hp_inj he))

/-- Coverage is a genuine partition: a vertex cannot belong to two selected blocks. -/
theorem unique_member (h : SelectionTrace edge pressure R L)
    (b : Block V) (hb : b ∈ L) (c : Block V) (hc : c ∈ L)
    (v : V) (hvb : v ∈ b.members) (hvc : v ∈ c.members) : b = c := by
  induction h generalizing b c with
  | nil => simp at hb
  | cons R q _ _ tail ht ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact False.elim ((mem_sdiff.mp (ht.members_subset c hc hvc)).2 hvb)
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact False.elim ((mem_sdiff.mp (ht.members_subset b hb hvb)).2 hvc)
        · exact ih b hb c hc hvb hvc

/-- At least one vertex is removed at each recursive step. -/
theorem length_le_card (h : SelectionTrace edge pressure R L) : L.length ≤ R.card := by
  induction h with
  | nil => simp
  | cons R q hq _ tail _ ih =>
      have hd : (R \ predecessorBlock edge R q).card < R.card := by
        apply card_lt_card
        apply sdiff_ssubset (predecessorBlock_subset edge R q)
        exact ⟨q, root_mem_predecessorBlock edge R q hq⟩
      exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hd)

end SelectionTrace

/-- The algorithm gives an actual partition with root paths and cross-block order. -/
theorem blocks_spec (edge : V → V → Prop) (pressure : V → ℝ) (R : Finset V) :
    (∀ v, (∃ b ∈ blocks edge pressure R, v ∈ b.members) ↔ v ∈ R) ∧
    (blocks edge pressure R).Pairwise (fun b c => Disjoint b.members c.members) ∧
    (∀ b ∈ blocks edge pressure R, b.root ∈ b.members ∧
      ∀ v ∈ b.members, ReflTransGen edge v b.root ∧ pressure v ≤ pressure b.root) ∧
    (blocks edge pressure R).Pairwise
      (fun b c => ∀ x ∈ c.members, ∀ y ∈ b.members, ¬ReflTransGen edge x y) ∧
    (blocks edge pressure R).length ≤ R.card := by
  have ht := blocks_selectionTrace edge pressure R
  refine ⟨ht.covers, ht.pairwise_disjoint, ?_, ht.pairwise_no_backward_reach, ht.length_le_card⟩
  intro b hb
  refine ⟨ht.root_mem b hb, ?_⟩
  intro v hv
  exact ⟨ht.reaches_root b hb v hv, ht.pressure_le_root b hb v hv⟩

theorem exists_unique_block (edge : V → V → Prop) (pressure : V → ℝ)
    (R : Finset V) (v : V) (hv : v ∈ R) :
    ∃! b : Block V, b ∈ blocks edge pressure R ∧ v ∈ b.members := by
  have ht := blocks_selectionTrace edge pressure R
  obtain ⟨b, hb, hvb⟩ := (ht.covers v).mpr hv
  refine ⟨b, ⟨hb, hvb⟩, ?_⟩
  rintro c ⟨hc, hvc⟩
  exact ht.unique_member c hc b hb v hvc hvb

theorem blocks_length_pos (edge : V → V → Prop) (pressure : V → ℝ)
    (R : Finset V) (hR : R.Nonempty) : 0 < (blocks edge pressure R).length := by
  classical
  rw [blocks, dite_eq_left hR]
  exact Nat.succ_pos _

/-- In a finite vertex type every vertex receives exactly one pressure-selected root. -/
theorem exists_unique_block_univ [Fintype V] (edge : V → V → Prop) (pressure : V → ℝ)
    (v : V) : ∃! b : Block V, b ∈ blocks edge pressure univ ∧ v ∈ b.members :=
  exists_unique_block edge pressure univ v (mem_univ v)

theorem blocks_univ_length_bounds [Fintype V] [Nonempty V]
    (edge : V → V → Prop) (pressure : V → ℝ) :
    0 < (blocks edge pressure univ).length ∧
      (blocks edge pressure univ).length ≤ Fintype.card V := by
  refine ⟨blocks_length_pos edge pressure univ univ_nonempty, ?_⟩
  simpa only [card_univ] using (blocks_selectionTrace edge pressure univ).length_le_card

end LeanShared.PressureBlocks
