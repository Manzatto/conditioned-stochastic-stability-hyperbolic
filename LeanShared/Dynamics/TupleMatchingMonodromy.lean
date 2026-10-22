module

public import LeanShared.Dynamics.TupleMatchingReindex

/-! Permutation monodromy of an ordered tuple becomes an ordinary
periodic walk in the signed matching graph.  The product of actual edge
signs is exactly the monodromy sign, by telescoping canonical orderings.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [DecidableEq A] {R E : A → A → Prop} {k : ℕ}

theorem tupleOrdering_congr (u v : Fin k → A) (hu : Injective u) (hv : Injective v)
    (eu : ∀ i j, E (u i) (u j)) (ev : ∀ i j, E (v i) (v j)) (equal : u = v) :
    tupleOrdering u hu eu = tupleOrdering v hv ev := by
  subst v
  rfl

theorem tupleMatchingEdge_congr (u v u' v' : Fin k → A)
    (h : FiberTupleTransition R E k u v) (h' : FiberTupleTransition R E k u' v')
    (source : u = u') (target : v = v') :
    tupleMatchingEdge u v h.2.2.2.1 h.2.2.2.2 h.2.1 h.2.2.1 h.1 =
      tupleMatchingEdge u' v' h'.2.2.2.1 h'.2.2.2.2 h'.2.1 h'.2.2.1 h'.1 := by
  subst u'
  subst v'
  rfl

@[expose] def matchingEdgeSign (e : SubsetMatchingEdge R E k) : ℤˣ := Equiv.Perm.sign e.val.2.2

@[expose] def tuplePathOrdering (a : Path (FiberTupleTransition R E k)) (n : ℤ) : Equiv.Perm (Fin k) :=
  tupleOrdering (a.val n) (a.property n).2.2.2.1 (a.property n).2.1

theorem tupleMatching_edge_sign (a : Path (FiberTupleTransition R E k)) (n : ℤ) :
    matchingEdgeSign ((tupleToMatchingPath a).val n) =
      Equiv.Perm.sign (tuplePathOrdering a (n + 1)) / Equiv.Perm.sign (tuplePathOrdering a n) := by
  change Equiv.Perm.sign ((tuplePathOrdering a (n + 1)).trans (tuplePathOrdering a n).symm) = _
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, div_eq_mul_inv, Int.units_inv_eq_self, mul_comm]

theorem tupleMatching_sign_product (a : Path (FiberTupleTransition R E k)) (n : ℕ) :
    (∏ i ∈ Finset.range n, matchingEdgeSign ((tupleToMatchingPath a).val i)) =
      Equiv.Perm.sign (tuplePathOrdering a n) / Equiv.Perm.sign (tuplePathOrdering a 0) := by
  calc
    _ = ∏ i ∈ Finset.range n, Equiv.Perm.sign (tuplePathOrdering a (i + 1 : ℕ)) /
        Equiv.Perm.sign (tuplePathOrdering a i) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Nat.cast_add, Nat.cast_one] using tupleMatching_edge_sign a i
    _ = _ := Finset.prod_range_div (fun i : ℕ => Equiv.Perm.sign (tuplePathOrdering a i)) n

theorem tupleMatching_periodic_of_monodromy (a : Path (FiberTupleTransition R E k))
    (period : ℤ) (q : Equiv.Perm (Fin k))
    (monodromy : ∀ n : ℤ, a.val (n + period) = a.val n ∘ q) :
    Function.Periodic (tupleToMatchingPath a).val period := by
  intro n
  have next : a.val (n + period + 1) = a.val (n + 1) ∘ q := by
    rw [add_right_comm]
    exact monodromy (n + 1)
  have reindexed : FiberTupleTransition R E k (a.val n ∘ q) (a.val (n + 1) ∘ q) :=
    ⟨fun i => (a.property n).1 (q i), fun i j => (a.property n).2.1 (q i) (q j),
      fun i j => (a.property n).2.2.1 (q i) (q j),
      (a.property n).2.2.2.1.comp q.injective, (a.property n).2.2.2.2.comp q.injective⟩
  exact (tupleMatchingEdge_congr (a.val (n + period)) (a.val (n + period + 1))
    (a.val n ∘ q) (a.val (n + 1) ∘ q) (a.property (n + period)) reindexed
    (monodromy n) next).trans
    (tupleMatchingEdge_reindex (a.val n) (a.val (n + 1))
      (a.property n).2.2.2.1 (a.property n).2.2.2.2
      (a.property n).2.1 (a.property n).2.2.1 (a.property n).1 q)

theorem tupleMatching_sign_monodromy (a : Path (FiberTupleTransition R E k))
    (period : ℕ) (q : Equiv.Perm (Fin k))
    (monodromy : ∀ n : ℤ, a.val (n + period) = a.val n ∘ q) :
    (∏ i ∈ Finset.range period, matchingEdgeSign ((tupleToMatchingPath a).val i)) = Equiv.Perm.sign q := by
  rw [tupleMatching_sign_product]
  have atZero := monodromy 0
  simp only [zero_add] at atZero
  have ordering : tuplePathOrdering a period = (tuplePathOrdering a 0).trans q.symm := by
    exact (tupleOrdering_congr (a.val period) (a.val 0 ∘ q)
      (a.property period).2.2.2.1 ((a.property 0).2.2.2.1.comp q.injective)
      (a.property period).2.1 (fun i j => (a.property 0).2.1 (q i) (q j)) atZero).trans
      (tupleOrdering_reindex (a.val 0) (a.property 0).2.2.2.1 (a.property 0).2.1 q)
  rw [ordering, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_div_cancel_right]

end LeanShared.BilateralShadowingCoding
