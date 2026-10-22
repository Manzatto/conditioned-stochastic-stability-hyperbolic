module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Order.Lattice.Nat

/-! Maximal-cardinality actual Bowen separated sets span the state space;
only a proved finite cardinal bound is needed. -/
public noncomputable section
open Set Function
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [Nonempty X]

theorem exists_separated_spanning (T : X → X) (n : ℕ) (ε : ℝ) (positive : 0 < ε)
    (C : ℕ) (count : ∀ s : Finset X, Separated T univ n ε s → s.card ≤ C) :
    ∃ s : Finset X, s.Nonempty ∧ Separated T univ n ε s ∧
      ∀ x : X, ∃ y ∈ s, ∀ j < n, dist (T^[j] x) (T^[j] y) < ε := by
  classical
  let cards : Set ℕ := {m | ∃ s : Finset X, Separated T univ n ε s ∧ s.card=m}
  have empty : Separated T univ n ε (∅ : Finset X) := by
    constructor <;> simp
  have bounded : BddAbove cards := by
    refine ⟨C,?_⟩
    rintro m ⟨s,hs,rfl⟩
    exact count s hs
  obtain ⟨s,separated,card⟩ := Nat.sSup_mem (s := cards) ⟨0,∅,empty,rfl⟩ bounded
  have maximal (q : Finset X) (hq : Separated T univ n ε q) : q.card ≤ s.card := by
    rw [card]
    exact le_csSup bounded ⟨q,hq,rfl⟩
  have nonempty : s.Nonempty := by
    let x : X := Classical.arbitrary X
    have singleton : Separated T univ n ε {x} := by
      refine ⟨fun _ _ => mem_univ _,?_⟩
      intro y hy z hz different
      exact (different ((Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm)).elim
    have lower := maximal {x} singleton
    have : 0 < s.card := by simpa using lower
    exact Finset.card_pos.mp this
  refine ⟨s,nonempty,separated,?_⟩
  intro x
  by_contra failure
  have far : ∀ y ∈ s, ∃ j < n, ε ≤ dist (T^[j] x) (T^[j] y) := by
    push Not at failure
    simpa only [exists_prop] using failure
  have absent : x ∉ s := by
    intro hx
    obtain ⟨j,_,bad⟩ := far x hx
    have impossible : (0 : ℝ) < 0 := by simpa only [dist_self] using positive.trans_le bad
    exact (lt_irrefl 0) impossible
  have enlarged : Separated T univ n ε (insert x s) := by
    refine ⟨fun _ _ => mem_univ _,?_⟩
    intro y hy z hz different
    rcases Finset.mem_insert.mp hy with hyx | hys
    · subst y
      rcases Finset.mem_insert.mp hz with hzx | hzs
      · exact (different hzx.symm).elim
      · exact far z hzs
    · rcases Finset.mem_insert.mp hz with hzx | hzs
      · subst z
        obtain ⟨j,hj,bound⟩ := far y hys
        exact ⟨j,hj,by simpa only [dist_comm] using bound⟩
      · exact separated.2 y hys z hzs different
  have impossible := maximal (insert x s) enlarged
  rw [Finset.card_insert_of_notMem absent] at impossible
  omega

end LeanShared.ThermodynamicDefinitions
