module
public import ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixEncoding

/-! The computed selected basins have exactly the manuscript's labelled
intervals. Coverage, topological reachability and separation force adjacent
prefix sizes to equal the preceding root; no indexing rule is assumed. -/
public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
open LeanShared PressureFiltrationSource
variable {I : Type*} {edge : I → I → Prop} {pressure : I → ℝ}
  (d : GreedyPrefixGeometry.Data edge pressure)

theorem edge_decreases (i j : Fin d.order.length)
    (e : edge (reversedVertex d.order i) (reversedVertex d.order j)) : j.val < i.val := by
  have ordered := d.topological
    ⟨d.order.length - 1 - i.val, by have h := i.isLt; omega⟩
    ⟨d.order.length - 1 - j.val, by have h := j.isLt; omega⟩ e
  change d.order.length - 1 - i.val < d.order.length - 1 - j.val at ordered
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem path_decreases (i j : Fin d.order.length)
    (path : ReflTransGen (fun a b => edge (reversedVertex d.order a) (reversedVertex d.order b)) i j) :
    j.val ≤ i.val := by
  induction path with
  | refl => exact le_rfl
  | @tail v w _ e ih => exact (d.edge_decreases v w e).le.trans ih

theorem exists_interval (j : Fin d.order.length) :
    ∃ s : Fin d.number, (d.root s).val ≤ j.val ∧ j.val < d.size s := by
  obtain ⟨s, i, same, path⟩ := d.assignment j
  have fullPath := ReflTransGen.lift
    (p := fun a b : Fin d.order.length => edge (reversedVertex d.order a) (reversedVertex d.order b))
    (fun a : Fin (d.size s) => (⟨a.val, a.isLt.trans_le (d.size_le s)⟩ : Fin d.order.length))
    (fun _ _ e => e) i (d.root s) path
  have lower := d.path_decreases _ _ fullPath
  refine ⟨s, ?_, ?_⟩
  · simpa only [same] using lower
  · exact same ▸ i.isLt

theorem interval_unique (s q : Fin d.number) (j : Fin d.order.length)
    (hs : (d.root s).val ≤ j.val ∧ j.val < d.size s)
    (hq : (d.root q).val ≤ j.val ∧ j.val < d.size q) : s = q := by
  by_contra different
  rcases lt_or_gt_of_ne different with before | after
  · have bound := d.root_above_later s q before
    omega
  · have bound := d.root_above_later q s after
    omega

theorem next_size_eq_root (s q : Fin d.number) (next : q.val = s.val + 1) :
    d.size q = (d.root s).val := by
  have before : s < q := by apply Fin.mk_lt_mk.mpr; omega
  have lower := d.root_above_later s q before
  apply le_antisymm lower
  by_contra hn
  have gap : d.size q < (d.root s).val := by omega
  have rootBound := (d.root s).isLt
  have sizeBound := d.size_le s
  let j : Fin d.order.length := ⟨d.size q, by omega⟩
  obtain ⟨r, low, high⟩ := d.exists_interval j
  change (d.root r).val ≤ d.size q at low
  change d.size q < d.size r at high
  by_cases hr : r < q
  · by_cases same : r = s
    · subst r
      omega
    · have earlier : r < s := by apply Fin.mk_lt_mk.mpr; have _hr := hr; omega
      have rb := d.root_above_later r s earlier
      omega
  · by_cases same : r = q
    · subst r
      omega
    · have later : q < r := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm same)
      have rb := d.root_above_later q r later
      have rootq := (d.root q).isLt
      omega

theorem last_root_zero (s : Fin d.number) (last : s.val + 1 = d.number) : (d.root s).val = 0 := by
  by_contra hn
  have rootBound := (d.root s).isLt
  have sizeBound := d.size_le s
  let j : Fin d.order.length := ⟨0, by omega⟩
  obtain ⟨r, low, _high⟩ := d.exists_interval j
  change (d.root r).val ≤ 0 at low
  by_cases same : r = s
  · subst r
    omega
  · have earlier : r < s := by apply Fin.mk_lt_mk.mpr; have bound := r.isLt; omega
    have rb := d.root_above_later r s earlier
    omega

/-- A basic index in its prescribed interval reaches that very selected
root within its literal prefix. The existential assignment is eliminated. -/
theorem interval_reachable (s : Fin d.number) (j : Fin d.order.length)
    (lower : (d.root s).val ≤ j.val) (upper : j.val < d.size s) :
    ReflTransGen (fun a b : Fin (d.size s) =>
      edge (reversedVertex d.order ⟨a.val, a.isLt.trans_le (d.size_le s)⟩)
        (reversedVertex d.order ⟨b.val, b.isLt.trans_le (d.size_le s)⟩))
      ⟨j.val, upper⟩ (d.root s) := by
  obtain ⟨q, i, same, path⟩ := d.assignment j
  have fullPath := ReflTransGen.lift
    (p := fun a b : Fin d.order.length => edge (reversedVertex d.order a) (reversedVertex d.order b))
    (fun a : Fin (d.size q) => (⟨a.val, a.isLt.trans_le (d.size_le q)⟩ : Fin d.order.length))
    (fun _ _ e => e) i (d.root q) path
  have bound := d.path_decreases _ _ fullPath
  have qlow : (d.root q).val ≤ j.val := by simpa only [same] using bound
  have qupper : j.val < d.size q := same ▸ i.isLt
  have equal := d.interval_unique s q j ⟨lower, upper⟩ ⟨qlow, qupper⟩
  subst q
  have sameIndex : i = ⟨j.val, upper⟩ := Fin.ext same.symm
  exact sameIndex ▸ path
end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
