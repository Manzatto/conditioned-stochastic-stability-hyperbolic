module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualHG2Selection
public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixReachability

/-! The actual greedy blocks have one common reversed filtration order.
Its residual suffixes determine every prefix, selected root, pressure gap
and internal reachability. These are derived finite conclusions, not input
filtration or geometric certificates. -/
public noncomputable section
open Set Relation Function
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
open LeanShared PressureBlocks PressureTopologicalOrder PressureFiltrationSource
open PressurePrefixSelection PressurePrefixReachability ActualHG2Selection
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
private theorem reversed_index_ge_suffix (before suffix : List I)
    (i : Fin (before ++ suffix).length)
    (h : reversedVertex (before ++ suffix) i ∉ suffix) : suffix.length ≤ i.val := by
  by_contra hn
  have hi : i.val < suffix.length := by omega
  exact h (reversed_prefix_mem_suffix before suffix ⟨i.val, hi⟩)

private theorem drop_order_length_le
    (edge : I → I → Prop) (pressure : I → ℝ) (wf : WellFounded (TransGen edge))
    (B : List (Block I)) {m n : ℕ} (hmn : m ≤ n) :
    (blockOrder edge pressure wf (B.drop n)).length ≤
      (blockOrder edge pressure wf (B.drop m)).length := by
  have split := blockOrder_take_drop edge pressure wf (B.drop m) (n - m)
  have dropped : (B.drop m).drop (n - m) = B.drop n := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [dropped] at split
  rw [split, List.length_append]
  omega

omit [DecidableEq I] in
private theorem vertex_of_split (L before suffix : List I) (split : L = before ++ suffix)
    (i : Fin suffix.length) (hi : i.val < L.length) :
    reversedVertex L ⟨i.val, hi⟩ = reversedVertex suffix i := by
  subst L
  exact reversedVertex_append_suffix before suffix i

private theorem full_prefix_vertex
    (edge : I → I → Prop) (pressure : I → ℝ) (wf : WellFounded (TransGen edge))
    (B : List (Block I)) (n : ℕ)
    (i : Fin (blockOrder edge pressure wf (B.drop n)).length) :
    reversedVertex (blockOrder edge pressure wf B)
      ⟨i.val, lt_of_lt_of_le i.isLt (drop_order_length_le edge pressure wf B (Nat.zero_le n))⟩ =
    reversedVertex (blockOrder edge pressure wf (B.drop n)) i := by
  have split := blockOrder_take_drop edge pressure wf B n
  exact vertex_of_split _ _ _ split i _

/-- All indices are literal prefixes of one derived finite order. -/
structure Data (edge : I → I → Prop) (pressure : I → ℝ) where
  order : List I
  cover : ∀ v : I, v ∈ order
  nodup : order.Nodup
  topological : ∀ i j : Fin order.length, edge (order.get i) (order.get j) → i < j
  number : ℕ
  number_positive : Nonempty I → 0 < number
  size : Fin number → ℕ
  size_positive : ∀ s, 0 < size s
  size_le : ∀ s, size s ≤ order.length
  root : ∀ s, Fin (size s)
  pressure_gap : ∀ s (i : Fin (size s)), i ≠ root s →
    pressure (reversedVertex order ⟨i.val, lt_of_lt_of_le i.isLt (size_le s)⟩) <
      pressure (reversedVertex order ⟨(root s).val, lt_of_lt_of_le (root s).isLt (size_le s)⟩)
  root_above_later : ∀ s q : Fin number, s < q → size q ≤ (root s).val
  assignment : ∀ j : Fin order.length, ∃ s : Fin number, ∃ i : Fin (size s),
    j.val = i.val ∧
    ReflTransGen (fun a b : Fin (size s) => edge
      (reversedVertex order ⟨a.val, lt_of_lt_of_le a.isLt (size_le s)⟩)
      (reversedVertex order ⟨b.val, lt_of_lt_of_le b.isLt (size_le s)⟩)) i (root s)

private theorem residual_root [Fintype I]
    (edge : I → I → Prop) (pressure : I → ℝ)
    (acyclic : ∀ v, ¬TransGen edge v v) (distinct : Injective pressure)
    (n : Fin (blocks edge pressure Finset.univ).length) :
    let B := blocks edge pressure Finset.univ
    let wf := wellFounded_of_acyclic edge acyclic
    ∃ j : Fin (blockOrder edge pressure wf (B.drop n.val)).length,
      reversedVertex (blockOrder edge pressure wf (B.drop n.val)) j = (B.get n).root ∧
      (∀ i : Fin (blockOrder edge pressure wf (B.drop n.val)).length, i ≠ j →
        pressure (reversedVertex (blockOrder edge pressure wf (B.drop n.val)) i) <
          pressure (B.get n).root) ∧
      (∀ i : Fin (blockOrder edge pressure wf (B.drop n.val)).length,
        reversedVertex (blockOrder edge pressure wf (B.drop n.val)) i ∈ (B.get n).members →
        ReflTransGen (fun a b => edge
          (reversedVertex (blockOrder edge pressure wf (B.drop n.val)) a)
          (reversedVertex (blockOrder edge pressure wf (B.drop n.val)) b)) i j) ∧
      (blockOrder edge pressure wf (B.drop (n.val + 1))).length ≤ j.val := by
  dsimp only
  let B := blocks edge pressure Finset.univ
  let wf := wellFounded_of_acyclic edge acyclic
  let b := B.get n
  let tail := B.drop (n.val + 1)
  have drop : B.drop n.val = b :: tail := by
    simpa only [← List.get_eq_getElem] using List.drop_eq_getElem_cons n.isLt
  rw [drop]
  obtain ⟨residual, trace, _closed, _mem, j, root, gap, reach⟩ :=
    exists_actual_HG2_selected_prefix edge pressure acyclic distinct n.val b tail drop
  refine ⟨j, root, gap, reach, ?_⟩
  have rootMem : b.root ∈ b.members := trace.root_mem b (by simp)
  have pair := (List.pairwise_cons.mp trace.pairwise_disjoint).1
  have notTail : b.root ∉ blockOrder edge pressure wf tail := by
    intro hv
    obtain ⟨c, hc, member⟩ := (mem_blockOrder edge pressure wf tail b.root).mp hv
    exact Finset.disjoint_left.mp (pair c hc) rootMem member
  apply reversed_index_ge_suffix (priorityOrder edge pressure wf b.members)
    (blockOrder edge pressure wf tail) j
  simpa only [blockOrder, List.flatMap_cons] using (root.symm ▸ notTail)

/-- Construct every common prefix and assignment from the actual greedy
algorithm. All pressure, reachability and inter-prefix ordering fields are
proved outputs. -/
def ofGraph [Fintype I]
    (edge : I → I → Prop) (pressure : I → ℝ)
    (acyclic : ∀ v, ¬TransGen edge v v) (distinct : Injective pressure) : Data edge pressure := by
  classical
  let B := blocks edge pressure Finset.univ
  let wf := wellFounded_of_acyclic edge acyclic
  let O := blockOrder edge pressure wf B
  let roots := fun n : Fin B.length => Classical.choose (residual_root edge pressure acyclic distinct n)
  have spec := fun n : Fin B.length => Classical.choose_spec (residual_root edge pressure acyclic distinct n)
  have bound : ∀ n : Fin B.length, (blockOrder edge pressure wf (B.drop n.val)).length ≤ O.length :=
    fun n => drop_order_length_le edge pressure wf B (Nat.zero_le n.val)
  have positive : ∀ n : Fin B.length, 0 < (blockOrder edge pressure wf (B.drop n.val)).length := by
    intro n
    exact lt_of_le_of_lt (Nat.zero_le (roots n).val) (roots n).isLt
  have trace : SelectionTrace edge pressure Finset.univ B := blocks_selectionTrace edge pressure Finset.univ
  have nodup : O.Nodup := BlockTrace.nodup trace wf
  refine {
    order := O
    cover := fun v => (mem_blockOrder edge pressure wf B v).mpr ((trace.covers v).mpr (Finset.mem_univ v))
    nodup := nodup
    topological := fun i j e => edge_indices wf (BlockTrace.pairwise_no_backward_path trace wf) i j e
    number := B.length
    number_positive := ?_
    size := fun n => (blockOrder edge pressure wf (B.drop n.val)).length
    size_positive := positive
    size_le := bound
    root := roots
    pressure_gap := ?_
    root_above_later := ?_
    assignment := ?_ }
  · intro nonempty
    let : Nonempty I := nonempty
    exact blocks_length_pos edge pressure Finset.univ Finset.univ_nonempty
  · intro n i different
    rw [full_prefix_vertex edge pressure wf B n.val i,
      full_prefix_vertex edge pressure wf B n.val (roots n), (spec n).1]
    exact (spec n).2.1 i different
  · intro n q less
    exact (drop_order_length_le edge pressure wf B (show n.val + 1 ≤ q.val by exact less)).trans
      (spec n).2.2.2
  · intro j
    let v := reversedVertex O j
    have hv : v ∈ Finset.univ := Finset.mem_univ v
    obtain ⟨b, hb, member⟩ := (trace.covers v).mpr hv
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp hb
    have drop : B.drop n.val = B.get n :: B.drop (n.val + 1) := by
      simpa only [← List.get_eq_getElem] using List.drop_eq_getElem_cons n.isLt
    have inResidual : v ∈ blockOrder edge pressure wf (B.drop n.val) := by
      apply (mem_blockOrder edge pressure wf (B.drop n.val) v).mpr
      refine ⟨B.get n, ?_, ?_⟩
      · rw [drop]
        exact List.mem_cons_self
      · rw [hn]
        exact member
    obtain ⟨i, hi⟩ := exists_reversed_prefix_index [] (blockOrder edge pressure wf (B.drop n.val)) v inResidual
    simp only [List.nil_append] at hi
    have fullVertex : reversedVertex O ⟨i.val, lt_of_lt_of_le i.isLt (bound n)⟩ = reversedVertex O j :=
      (full_prefix_vertex edge pressure wf B n.val i).trans hi
    have index := reversedVertex_injective O nodup fullVertex
    refine ⟨n, i, (congrArg Fin.val index).symm, ?_⟩
    have path := (spec n).2.2.1 i (by rw [hi, hn]; exact member)
    exact ReflTransGen.mono (fun a b e => by
      rw [full_prefix_vertex edge pressure wf B n.val a,
        full_prefix_vertex edge pressure wf B n.val b]
      exact e) i (roots n) path

end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
