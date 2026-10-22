module

public import Mathlib.Analysis.Normed.Operator.Mul

/-! Algebraic transfer words with one observation and the exact survival horizon. -/

@[expose] public noncomputable section

namespace LeanShared.TransferWords

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- Chronological transfer word, built from its terminal observable. -/
def word (P : B →L[ℝ] B) (φ : ℕ → B) : ℕ → B → B
  | 0, v => v
  | n + 1, v => word P φ n (φ n * P v)

/-- A unit observation at every time collapses the word to an operator power. -/
theorem word_eq_power (P : B →L[ℝ] B) (φ : ℕ → B) (n : ℕ)
    (hφ : ∀ i < n, φ i = 1) (v : B) : word P φ n v = (P ^ n) v := by
  induction n generalizing v with
  | zero => simp [word]
  | succ n ih =>
      rw [word, hφ n (by omega), one_mul, ih (fun i hi => hφ i (by omega))]
      rw [pow_succ]
      rfl

/-- The bounded-algebra observation at one designated time. -/
def singleObservation (i : ℕ) (h : B) (j : ℕ) : B := if j = i then h else 1

/-- A single observation at time `i < n` gives `P^i(h P^(n-i)v)` exactly. -/
theorem word_singleObservation (P : B →L[ℝ] B) (h : B) (i n : ℕ)
    (hin : i < n) (v : B) :
    word P (singleObservation i h) n v = (P ^ i) (h * (P ^ (n - i)) v) := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
      by_cases hi : i = n
      · subst i
        rw [word, singleObservation, ite_eq_left rfl]
        rw [word_eq_power P _ n (fun j hj => by
          simp only [singleObservation, ite_eq_right (Nat.ne_of_lt hj)])]
        simp only [Nat.add_sub_cancel_left, pow_one]
      · have hin' : i < n := by omega
        rw [word, singleObservation, ite_eq_right (Ne.symm hi), one_mul, ih hin']
        have hexp : n + 1 - i = (n - i) + 1 := by omega
        rw [hexp, pow_succ]
        rfl

end LeanShared.TransferWords
