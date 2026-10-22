module

public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection

/-! # Actual finite-prefix graph paths from greedy predecessor blocks

Removing a predecessor block preserves forward closure of the residual graph.
A graph path can therefore be lifted through the actual injective finite
prefix enumeration; no prefix reachability assertion is a source assumption.
-/
@[expose] public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixReachability
open LeanShared PressureBlocks PressureTopologicalOrder PressureFiltrationSource
variable {I : Type*} [DecidableEq I]

def ForwardClosed (edge : I → I → Prop) (R : Finset I) : Prop :=
  ∀ x ∈ R, ∀ y, edge x y → y ∈ R

omit [DecidableEq I] in
theorem forwardClosed_reachable (edge : I → I → Prop) (R : Finset I)
    (hclosed : ForwardClosed edge R) {x y : I} (hx : x ∈ R)
    (hxy : ReflTransGen edge x y) : y ∈ R := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact hclosed _ ih _ hstep

theorem forwardClosed_remove_predecessor (edge : I → I → Prop) (R : Finset I)
    (hclosed : ForwardClosed edge R) (q : I) :
    ForwardClosed edge (R \ predecessorBlock edge R q) := by
  intro x hx y hxy
  have hyR := hclosed x (Finset.mem_sdiff.mp hx).1 y hxy
  refine Finset.mem_sdiff.mpr ⟨hyR, ?_⟩
  intro hy
  exact remaining_not_reach_block edge R q x y hx hy (.single hxy)

theorem exists_forward_closed_residual
    (edge : I → I → Prop) (pressure : I → ℝ) (R : Finset I)
    (L : List (Block I)) (ht : SelectionTrace edge pressure R L)
    (hclosed : ForwardClosed edge R) (n : ℕ) :
    ∃ R' : Finset I, R' ⊆ R ∧ ForwardClosed edge R' ∧
      SelectionTrace edge pressure R' (L.drop n) := by
  induction n generalizing R L with
  | zero => exact ⟨R, Finset.Subset.rfl, hclosed, by simpa using ht⟩
  | succ n ih =>
    cases ht with
    | nil => exact ⟨∅, Finset.Subset.rfl, by simp [ForwardClosed], by simp; exact SelectionTrace.nil⟩
    | cons R q hq hp tail ht =>
      obtain ⟨R', hsub, hcl, htrace⟩ := ih _ _ ht (forwardClosed_remove_predecessor edge R hclosed q)
      exact ⟨R', hsub.trans Finset.sdiff_subset, hcl, by simpa using htrace⟩

omit [DecidableEq I] in
/-- A genuine path inside a forward-closed residual lifts to the exact
finite enumeration used for its filtration prefix. -/
theorem lift_reachable_to_prefix {J : Type*} (edge : I → I → Prop) (R : Finset I)
    (f : J → I) (hinj : Function.Injective f)
    (hmem : ∀ i, f i ∈ R) (hcover : ∀ v ∈ R, ∃ i, f i = v)
    (hclosed : ForwardClosed edge R) (i j : J)
    (hpath : ReflTransGen edge (f i) (f j)) :
    ReflTransGen (fun a b => edge (f a) (f b)) i j := by
  have aux : ∀ v, ReflTransGen edge (f i) v → ∀ j, f j = v →
      ReflTransGen (fun a b => edge (f a) (f b)) i j := by
    intro v hp
    induction hp with
    | refl =>
      intro j hj
      have hji : j = i := hinj hj
      subst j
      exact .refl
    | @tail v w hp hvw ih =>
      intro j hj
      obtain ⟨p, hpv⟩ := hcover v (forwardClosed_reachable edge R hclosed (hmem i) hp)
      exact (ih p hpv).tail (by simpa only [hpv, hj] using hvw)
  exact aux _ hpath j rfl

/-- The actual selected root index has strict pressure dominance on the
whole residual prefix and is reached, inside that same finite prefix, by
every basic set in its predecessor block. -/
theorem exists_actual_selected_prefix_root
    (edge : I → I → Prop) (pressure : I → ℝ) (hWF : WellFounded (TransGen edge))
    (R : Finset I) (b : Block I) (tail : List (Block I))
    (ht : SelectionTrace edge pressure R (b :: tail))
    (hclosed : ForwardClosed edge R) (hdistinct : Set.InjOn pressure (R : Set I)) :
    let L := blockOrder edge pressure hWF (b :: tail)
    ∃ j : Fin L.length, reversedVertex L j = b.root ∧
      (∀ i : Fin L.length, i ≠ j → pressure (reversedVertex L i) < pressure b.root) ∧
      ∀ i : Fin L.length, reversedVertex L i ∈ b.members →
        ReflTransGen (fun a c : Fin L.length => edge (reversedVertex L a) (reversedVertex L c)) i j := by
  dsimp only
  let L := blockOrder edge pressure hWF (b :: tail)
  have hmem : ∀ i : Fin L.length, reversedVertex L i ∈ R := by
    intro i
    exact (ht.covers _).mp ((mem_blockOrder edge pressure hWF _ _).mp (List.get_mem _ _))
  have hcover : ∀ v ∈ R, ∃ i : Fin L.length, reversedVertex L i = v := by
    intro v hv
    have hvL : v ∈ L := (mem_blockOrder edge pressure hWF _ _).mpr ((ht.covers _).mpr hv)
    obtain ⟨i, hi⟩ := PressurePrefixSelection.exists_reversed_prefix_index [] L v hvL
    exact ⟨i, by simpa only [List.nil_append] using hi⟩
  obtain ⟨j, hj, hpressure⟩ := PressurePrefixSelection.exists_selected_root_in_residual_order
    edge pressure hWF R b tail ht hdistinct
  refine ⟨j, hj, hpressure, ?_⟩
  intro i hi
  apply lift_reachable_to_prefix edge R (reversedVertex L)
    (PressurePrefixSelection.reversedVertex_injective L (BlockTrace.nodup ht hWF)) hmem hcover hclosed i j
  rw [hj]
  exact ht.reaches_root b (by simp) _ hi

end ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixReachability
