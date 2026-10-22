module

public import LeanShared.Dynamics.PressureBlocks
public import Mathlib.Order.WellFounded
public import Mathlib.Data.List.Nodup

/-!
# Pressure-priority topological enumeration

Choose a maximum-pressure vertex among the predecessor-free vertices of the
residual finite set, erase it, and repeat. Pressure comparison is restricted
to available sources; it cannot override a directed path. Combining these
orders with the literal predecessor blocks gives a total enumeration with
contiguous blocks and no backwards paths. Well-founded strict reachability
is the explicit acyclicity input; none of the ordering conclusions is input.
-/

@[expose] public noncomputable section

open Finset Relation

namespace LeanShared.PressureTopologicalOrder

variable {V : Type*}

/-- On a finite vertex type, absence of nonempty directed cycles supplies the
well-foundedness required by the algorithm. -/
theorem wellFounded_of_acyclic [Finite V] (edge : V → V → Prop)
    (hacyclic : ∀ v, ¬TransGen edge v v) : WellFounded (TransGen edge) := by
  let : Std.Irrefl (TransGen edge) := ⟨hacyclic⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- Vertices with no strict predecessor remaining in the finite set. -/
def sources (edge : V → V → Prop) (R : Finset V) : Finset V := by
  classical
  exact R.filter (fun v => ∀ u ∈ R, ¬TransGen edge u v)

@[simp]
theorem mem_sources (edge : V → V → Prop) (R : Finset V) (v : V) :
    v ∈ sources edge R ↔ v ∈ R ∧ ∀ u ∈ R, ¬TransGen edge u v := by
  classical
  simp [sources]

theorem sources_nonempty (edge : V → V → Prop) (hWF : WellFounded (TransGen edge))
    (R : Finset V) (hR : R.Nonempty) : (sources edge R).Nonempty := by
  obtain ⟨q, hq, hp⟩ := hWF.has_min (↑R : Set V) hR
  exact ⟨q, (mem_sources edge R q).mpr ⟨hq, hp⟩⟩

/-- The pressure rule is applied only after enforcing the predecessor constraint. -/
def sourceMax (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) (hR : R.Nonempty) : V :=
  PressureBlocks.pressureMax pressure (sources edge R) (sources_nonempty edge hWF R hR)

theorem sourceMax_mem_sources (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) (hR : R.Nonempty) :
    sourceMax edge pressure hWF R hR ∈ sources edge R :=
  PressureBlocks.pressureMax_mem pressure _ _

theorem sourceMax_spec (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) (hR : R.Nonempty) :
    sourceMax edge pressure hWF R hR ∈ R ∧
      (∀ u ∈ R, ¬TransGen edge u (sourceMax edge pressure hWF R hR)) ∧
      ∀ v ∈ sources edge R, pressure v ≤ pressure (sourceMax edge pressure hWF R hR) := by
  exact ⟨((mem_sources edge R _).mp (sourceMax_mem_sources edge pressure hWF R hR)).1,
    ((mem_sources edge R _).mp (sourceMax_mem_sources edge pressure hWF R hR)).2,
    fun v hv => PressureBlocks.pressureMax_spec pressure _ _ v hv⟩

variable [DecidableEq V]

/-- The implemented cardinal-decreasing pressure-priority enumeration. -/
def priorityOrder (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) : List V :=
  if hR : R.Nonempty then
    let q := sourceMax edge pressure hWF R hR
    q :: priorityOrder edge pressure hWF (R.erase q)
  else []
termination_by R.card
decreasing_by exact card_erase_lt_of_mem (sourceMax_spec edge pressure hWF R hR).1

/-- Raw choices of the algorithm, including maximality only among available sources. -/
inductive SourceTrace (edge : V → V → Prop) (pressure : V → ℝ) :
    Finset V → List V → Prop
  | nil : SourceTrace edge pressure ∅ []
  | cons (R : Finset V) (q : V) (hq : q ∈ R)
      (hs : ∀ u ∈ R, ¬TransGen edge u q)
      (hp : ∀ v ∈ sources edge R, pressure v ≤ pressure q) (tail : List V)
      (htail : SourceTrace edge pressure (R.erase q) tail) :
      SourceTrace edge pressure R (q :: tail)

theorem priorityOrder_sourceTrace (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) :
    SourceTrace edge pressure R (priorityOrder edge pressure hWF R) := by
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R.Nonempty
  · rw [priorityOrder, dite_eq_left hR]
    obtain ⟨hq, hs, hp⟩ := sourceMax_spec edge pressure hWF R hR
    exact SourceTrace.cons R _ hq hs hp _ (ih _ (erase_ssubset hq))
  · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    subst R
    rw [priorityOrder, dite_eq_right Finset.not_nonempty_empty]
    exact SourceTrace.nil

namespace SourceTrace

variable {edge : V → V → Prop} {pressure : V → ℝ} {R : Finset V} {L : List V}

theorem mem_iff (h : SourceTrace edge pressure R L) (v : V) : v ∈ L ↔ v ∈ R := by
  induction h with
  | nil => simp
  | cons R q hq _ _ tail _ ih =>
      simp only [List.mem_cons, ih, mem_erase]
      constructor
      · rintro (rfl | ⟨_, hv⟩)
        · exact hq
        · exact hv
      · intro hv
        by_cases he : v = q
        · exact Or.inl he
        · exact Or.inr ⟨he, hv⟩

theorem nodup (h : SourceTrace edge pressure R L) : L.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons R q _ _ _ tail ht ih =>
      apply List.nodup_cons.mpr
      exact ⟨fun hq => (mem_erase.mp ((ht.mem_iff q).mp hq)).1 rfl, ih⟩

/-- Earlier vertices cannot have a path from a later vertex. -/
theorem pairwise_no_backward_path (h : SourceTrace edge pressure R L) :
    L.Pairwise (fun earlier later => ¬TransGen edge later earlier) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q _ hs _ tail ht ih =>
      exact List.Pairwise.cons
        (fun v hv => hs v (mem_of_mem_erase ((ht.mem_iff v).mp hv))) ih

theorem length_eq_card (h : SourceTrace edge pressure R L) : L.length = R.card := by
  induction h with
  | nil => simp
  | cons R q hq _ _ tail _ ih =>
      rw [List.length_cons, ih, card_erase_of_mem hq]
      exact Nat.sub_add_cancel (card_pos.mpr ⟨q, hq⟩)

end SourceTrace

omit [DecidableEq V] in
/-- The pairwise formulation gives the usual numerical topological order:
every actual directed edge goes from a smaller list index to a larger one. -/
theorem edge_indices {edge : V → V → Prop} (hWF : WellFounded (TransGen edge))
    {L : List V} (hL : L.Pairwise (fun earlier later => ¬TransGen edge later earlier))
    (i j : Fin L.length) (hij : edge (L.get i) (L.get j)) : i < j := by
  by_contra hlt
  have hle : j ≤ i := le_of_not_gt hlt
  rcases lt_or_eq_of_le hle with hji | rfl
  · exact hL.rel_get_of_lt hji (TransGen.single hij)
  · have := hWF.irrefl
    exact irrefl_of (TransGen edge) _ (TransGen.single hij)

theorem priorityOrder_spec (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) :
    (∀ v, v ∈ priorityOrder edge pressure hWF R ↔ v ∈ R) ∧
    (priorityOrder edge pressure hWF R).Nodup ∧
    (priorityOrder edge pressure hWF R).Pairwise
      (fun earlier later => ¬TransGen edge later earlier) ∧
    (priorityOrder edge pressure hWF R).length = R.card :=
  let h := priorityOrder_sourceTrace edge pressure hWF R
  ⟨h.mem_iff, h.nodup, h.pairwise_no_backward_path, h.length_eq_card⟩

/-- Concatenate the actual source orders of the actual selected predecessor blocks. -/
def blockOrder (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (L : List (PressureBlocks.Block V)) : List V :=
  L.flatMap (fun b => priorityOrder edge pressure hWF b.members)

theorem mem_blockOrder (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (L : List (PressureBlocks.Block V)) (v : V) :
    v ∈ blockOrder edge pressure hWF L ↔ ∃ b ∈ L, v ∈ b.members := by
  simp only [blockOrder, List.mem_flatMap]
  exact exists_congr fun b => and_congr_right fun _ =>
    (priorityOrder_sourceTrace edge pressure hWF b.members).mem_iff v

namespace BlockTrace

variable {edge : V → V → Prop} {pressure : V → ℝ} {R : Finset V}
    {L : List (PressureBlocks.Block V)}

theorem nodup (h : PressureBlocks.SelectionTrace edge pressure R L)
    (hWF : WellFounded (TransGen edge)) : (blockOrder edge pressure hWF L).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun b _ => (priorityOrder_sourceTrace edge pressure hWF b.members).nodup, ?_⟩
  apply h.pairwise_disjoint.imp
  intro b c hbc
  change List.Disjoint (priorityOrder edge pressure hWF b.members)
    (priorityOrder edge pressure hWF c.members)
  rw [List.disjoint_left]
  intro v hvb hvc
  exact Finset.disjoint_left.mp hbc
    ((priorityOrder_sourceTrace edge pressure hWF b.members).mem_iff v |>.mp hvb)
    ((priorityOrder_sourceTrace edge pressure hWF c.members).mem_iff v |>.mp hvc)

theorem pairwise_no_backward_path (h : PressureBlocks.SelectionTrace edge pressure R L)
    (hWF : WellFounded (TransGen edge)) :
    (blockOrder edge pressure hWF L).Pairwise
      (fun earlier later => ¬TransGen edge later earlier) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons R q _ _ tail ht ih =>
      change (priorityOrder edge pressure hWF (PressureBlocks.predecessorBlock edge R q) ++
        blockOrder edge pressure hWF tail).Pairwise _
      apply List.pairwise_append.mpr
      refine ⟨(priorityOrder_sourceTrace edge pressure hWF _).pairwise_no_backward_path,
        ih, ?_⟩
      intro y hy x hx
      obtain ⟨b, hb, hxb⟩ := (mem_blockOrder edge pressure hWF tail x).mp hx
      have hxR := ht.members_subset b hb hxb
      have hyB := (priorityOrder_sourceTrace edge pressure hWF _).mem_iff y |>.mp hy
      exact fun hxy => PressureBlocks.remaining_not_reach_block edge R q x y hxR hyB
        hxy.to_reflTransGen

end BlockTrace

/-- The complete pressure-block/source algorithm enumerates the original finite
set once, with no backwards path. Each block is a contiguous segment by construction. -/
theorem pressureBlocks_order_spec (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) :
    (∀ v, v ∈ blockOrder edge pressure hWF (PressureBlocks.blocks edge pressure R) ↔ v ∈ R) ∧
    (blockOrder edge pressure hWF (PressureBlocks.blocks edge pressure R)).Nodup ∧
    (blockOrder edge pressure hWF (PressureBlocks.blocks edge pressure R)).Pairwise
      (fun earlier later => ¬TransGen edge later earlier) := by
  let h := PressureBlocks.blocks_selectionTrace edge pressure R
  exact ⟨fun v => (mem_blockOrder edge pressure hWF _ v).trans (h.covers v),
    BlockTrace.nodup h hWF, BlockTrace.pairwise_no_backward_path h hWF⟩

theorem pressureBlocks_order_length (edge : V → V → Prop) (pressure : V → ℝ)
    (hWF : WellFounded (TransGen edge)) (R : Finset V) :
    (blockOrder edge pressure hWF (PressureBlocks.blocks edge pressure R)).length = R.card := by
  obtain ⟨hcover, hn, _⟩ := pressureBlocks_order_spec edge pressure hWF R
  have he : (blockOrder edge pressure hWF (PressureBlocks.blocks edge pressure R)).toFinset = R := by
    ext v
    simpa only [List.mem_toFinset] using hcover v
  rw [← List.toFinset_card_of_nodup hn, he]

/-- The finite, acyclic version needs no separate well-foundedness input. -/
theorem acyclic_pressureBlocks_order_spec [Finite V] (edge : V → V → Prop)
    (pressure : V → ℝ) (hacyclic : ∀ v, ¬TransGen edge v v) (R : Finset V) :
    let L := blockOrder edge pressure (wellFounded_of_acyclic edge hacyclic)
      (PressureBlocks.blocks edge pressure R)
    (∀ v, v ∈ L ↔ v ∈ R) ∧ L.Nodup ∧
      (∀ i j : Fin L.length, edge (L.get i) (L.get j) → i < j) := by
  dsimp only
  obtain ⟨hcover, hn, hp⟩ :=
    pressureBlocks_order_spec edge pressure (wellFounded_of_acyclic edge hacyclic) R
  exact ⟨hcover, hn, fun i j hij => edge_indices
    (wellFounded_of_acyclic edge hacyclic) hp i j hij⟩

end LeanShared.PressureTopologicalOrder
