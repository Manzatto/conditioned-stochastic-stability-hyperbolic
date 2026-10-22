module

public import LeanShared.Dynamics.FiniteExpansiveWords
public import Mathlib.Data.Fintype.Prod

/-! An arbitrarily long coarse Bowen tube contains a uniformly bounded
number of finer separated points. Only two finite boundary words are
needed; no bound grows with the observed horizon. -/
public noncomputable section
open Function Set
namespace LeanShared.FiniteExpansiveWords
variable {X J : Type*} [MetricSpace X]

private theorem backward_at_forward (T : X ≃ₜ X) (j i : ℕ) (x : X) :
    (T.symm : X → X)^[j] ((T : X → X)^[i] x) =
      if j ≤ i then (T : X → X)^[i - j] x else (T.symm : X → X)^[j - i] x := by
  split_ifs with h
  · have split : (T : X → X)^[i] x =
        (T : X → X)^[j] ((T : X → X)^[i - j] x) := by
      rw [← iterate_add_apply, Nat.add_sub_of_le h]
    rw [split]
    exact T.left_inv.iterate j _
  · have hji : i ≤ j := (Nat.le_of_not_ge h)
    have split : (T.symm : X → X)^[j] ((T : X → X)^[i] x) =
        (T.symm : X → X)^[j - i] ((T.symm : X → X)^[i] ((T : X → X)^[i] x)) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel hji]
    rw [split]
    exact congrArg ((T.symm : X → X)^[j - i]) (T.left_inv.iterate i x)

set_option maxHeartbeats 1600000 in
theorem separated_tube_card_le [Fintype J] (T : X ≃ₜ X) (label : X → J)
    (c ε : ℝ) (N : ℕ)
    (mesh : ∀ x y, label x = label y → dist x y ≤ c)
    (detects : ∀ x y, (∀ j ≤ N,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → dist x y < ε)
    (n : ℕ) (s : Finset X) (separated : ThermodynamicDefinitions.Separated T univ n ε s)
    (tube : ∀ x ∈ s, ∀ y ∈ s, ∀ i < n,
      dist ((T : X → X)^[i] x) ((T : X → X)^[i] y) ≤ c) :
    s.card ≤ (Fintype.card J) ^ (2 * N) := by
  let before := fun x : X => fun j : Fin N => label ((T.symm : X → X)^[j.val + 1] x)
  let after := fun x : X => fun j : Fin N => label ((T : X → X)^[n + j.val] x)
  have injective : Function.Injective (fun x : s => (before x.val, after x.val)) := by
    intro x y equal
    apply Subtype.ext
    by_contra different
    obtain ⟨i, hi, apart⟩ := separated.2 x.val x.property y.val y.property different
    have near := detects ((T : X → X)^[i] x.val) ((T : X → X)^[i] y.val) (by
      intro j hj
      constructor
      · rw [← iterate_add_apply, ← iterate_add_apply]
        by_cases inside : j + i < n
        · exact tube _ x.property _ y.property _ inside
        · have bound : j + i - n < N := by omega
          have labels := congrFun (congrArg Prod.snd equal) ⟨j + i - n, bound⟩
          have index : n + (j + i - n) = j + i := by omega
          exact mesh _ _ (by simpa only [after, index] using labels)
      · rw [backward_at_forward, backward_at_forward]
        by_cases lower : j ≤ i
        · rw [ite_eq_left lower, ite_eq_left lower]
          exact tube _ x.property _ y.property _ (by omega)
        · rw [ite_eq_right lower, ite_eq_right lower]
          have bound : j - i - 1 < N := by omega
          have labels := congrFun (congrArg Prod.fst equal) ⟨j - i - 1, bound⟩
          have index : j - i - 1 + 1 = j - i := by omega
          exact mesh _ _ (by simpa only [before, index] using labels))
    exact (not_lt_of_ge apart) near
  have count := Fintype.card_le_of_injective _ injective
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    two_mul, pow_add] using count

end LeanShared.FiniteExpansiveWords
