module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-! A finite-alphabet path family with no finite-window diamonds has at
most the square of the alphabet cardinality.  Finite families are
distinguished on a common finite window, whose two endpoint labels give
an injective map to a pair of symbols.  Infinite families contradict the
same bound on finite subsets.
-/

public noncomputable section
namespace LeanShared.FiniteEndpointCoding
open Set Function
variable {P I : Type*} [Fintype I]

theorem finite_card_bound (val : P → ℤ → I) (injectiveVal : Injective val) (S : Set P)
    (noDiamonds : ∀ a ∈ S, ∀ b ∈ S, ∀ radius : ℕ,
      val a (-(radius : ℤ)) = val b (-(radius : ℤ)) → val a radius = val b radius →
      ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → val a k = val b k) :
    S.Finite ∧ S.ncard ≤ (Fintype.card I) ^ 2 := by
  classical
  have finsetBound (s : Finset P) (subset : (s : Set P) ⊆ S) : s.card ≤ (Fintype.card I) ^ 2 := by
    have distinct (a b : s) (different : a ≠ b) : ∃ k : ℤ, val a.val k ≠ val b.val k := by
      by_contra none
      apply different
      apply Subtype.ext
      apply injectiveVal
      funext k
      exact not_ne_iff.mp (fun h => none ⟨k, h⟩)
    let separation (a b : s) : ℤ := if h : a = b then 0 else Classical.choose (distinct a b h)
    let radius : ℕ := Finset.univ.sup (fun p : s × s => (separation p.1 p.2).natAbs)
    let endpoint (a : s) : I × I := (val a.val (-(radius : ℤ)), val a.val radius)
    have injectiveEndpoint : Injective endpoint := by
      intro a b same
      by_contra different
      have lower : (separation a b).natAbs ≤ radius :=
        Finset.le_sup (f := fun p : s × s => (separation p.1 p.2).natAbs) (Finset.mem_univ (a, b))
      have atWitness := noDiamonds a.val (subset a.property) b.val (subset b.property) radius
        (congrArg Prod.fst same) (congrArg Prod.snd same) (separation a b) (by omega) (by omega)
      have differs : val a.val (separation a b) ≠ val b.val (separation a b) := by
        simpa only [separation, dite_eq_right different] using Classical.choose_spec (distinct a b different)
      exact differs atWitness
    have bound := Fintype.card_le_of_injective endpoint injectiveEndpoint
    simpa only [Fintype.card_coe, Fintype.card_prod, pow_two] using bound
  have finite : S.Finite := by
    by_contra infinite
    obtain ⟨s, subset, card⟩ := Set.Infinite.exists_subset_card_eq infinite ((Fintype.card I) ^ 2 + 1)
    have bound := finsetBound s subset
    omega
  refine ⟨finite, ?_⟩
  rw [Set.ncard_eq_toFinset_card S finite]
  exact finsetBound finite.toFinset (by simp only [Set.Finite.coe_toFinset]; exact subset_rfl)

end LeanShared.FiniteEndpointCoding
