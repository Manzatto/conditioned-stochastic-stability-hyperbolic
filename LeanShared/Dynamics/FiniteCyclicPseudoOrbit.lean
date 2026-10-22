module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! A finite cyclic pseudo-orbit gives an actual periodic bilateral
reference, including the closing jump. Genuine near-return orbit segments
produce these words with only one nonzero pseudo-orbit error. -/
public section
namespace LeanShared.FiniteCyclicPseudoOrbit
variable {X : Type*} [MetricSpace X]

@[expose] def reference {p : ℕ} (word : ZMod p → X) (n : ℤ) : X := word ((-n : ℤ) : ZMod p)

omit [MetricSpace X] in
theorem reference_periodic {p : ℕ} (word : ZMod p → X) (n : ℤ) :
    reference word (n + (p : ℤ)) = reference word n := by
  simp [reference, Int.cast_add, Int.cast_neg]

theorem reference_step {p : ℕ} (T : X → X) (word : ZMod p → X) (η : ℝ)
    (steps : ∀ i, dist (T (word i)) (word (i + 1)) < η) (n : ℤ) :
    dist (T (reference word (n + 1))) (reference word n) < η := by
  have index : ((-(n + 1) : ℤ) : ZMod p) + 1 = ((-n : ℤ) : ZMod p) := by push_cast; ring
  have result := steps ((-(n + 1) : ℤ) : ZMod p)
  rw [index] at result
  exact result

theorem orbit_word_step (T : X → X) (p : ℕ) (positiveP : 0 < p) (x : X)
    (η : ℝ) (positiveη : 0 < η) (closing : dist (T^[p] x) x < η) :
    ∀ i : ZMod p, dist (T (T^[i.val] x)) (T^[(i + 1).val] x) < η := by
  let _ : NeZero p := ⟨positiveP.ne'⟩
  intro i
  have castSuccessor : ((i.val + 1 : ℕ) : ZMod p) = i + 1 := by simp only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  by_cases small : i.val + 1 < p
  · have successor : (i + 1).val = i.val + 1 := by
      rw [← castSuccessor]
      exact ZMod.val_cast_of_lt small
    rw [successor, Function.iterate_succ_apply']
    simpa only [dist_self] using positiveη
  · have terminal : i.val + 1 = p := by have := ZMod.val_lt i; omega
    have successor : i + 1 = 0 := by rw [← castSuccessor, terminal]; exact ZMod.natCast_self p
    rw [successor, ZMod.val_zero, Function.iterate_zero_apply]
    have step : T (T^[i.val] x) = T^[p] x := by
      rw [← Function.iterate_succ_apply' T i.val x]
      exact congrArg (fun k => T^[k] x) terminal
    rw [step]
    exact closing

end LeanShared.FiniteCyclicPseudoOrbit
