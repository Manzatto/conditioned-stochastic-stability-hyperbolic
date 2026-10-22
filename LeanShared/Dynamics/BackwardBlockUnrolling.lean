module
public import LeanShared.Analysis.FiniteJetWords
public import Mathlib.Data.Nat.Basic

/-! Exact unrolling of a backward orbit of finite forward words into a
one-step backward orbit. The control index at each step is the original
backward time, including block endpoints. -/
public noncomputable section
namespace LeanShared.BackwardBlockUnrolling
open FiniteJetComposition

@[expose] def block {X : Type*} (f : ℕ → X → X) (N n j : ℕ) : X → X :=
  f (N * (n + 1) - 1 - j)

@[expose] def unroll {X : Type*} (f : ℕ → X → X) (N : ℕ) (b : ℕ → X) (m : ℕ) : X :=
  word (block f N (m / N)) (N - m % N) (b (m / N + 1))

private theorem grid {X : Type*} (f : ℕ → X → X) (N : ℕ) (positive : 0 < N)
    (b : ℕ → X) (step : ∀ n, word (block f N n) N (b (n + 1)) = b n)
    (q r : ℕ) (small : r ≤ N) :
    unroll f N b (N * q + r) = word (block f N q) (N - r) (b (q + 1)) := by
  rcases lt_or_eq_of_le small with strict | equal
  · simp only [unroll, Nat.mul_add_div positive, Nat.div_eq_of_lt strict,
      add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt strict]
  · rw [equal]
    have boundary : N * q + N = N * (q + 1) := (Nat.mul_succ N q).symm
    rw [boundary]
    simp only [unroll, Nat.mul_div_right _ positive, Nat.mul_mod_right,
      Nat.sub_zero, Nat.sub_self, word, id_eq]
    exact step (q + 1)

theorem zero {X : Type*} (f : ℕ → X → X) (N : ℕ) (b : ℕ → X)
    (step : ∀ n, word (block f N n) N (b (n + 1)) = b n) :
    unroll f N b 0 = b 0 := by
  simpa only [unroll, Nat.zero_div, Nat.zero_mod, Nat.sub_zero, zero_add] using step 0

theorem at_block {X : Type*} (f : ℕ → X → X) (N : ℕ) (positive : 0 < N)
    (b : ℕ → X) (step : ∀ n, word (block f N n) N (b (n + 1)) = b n) (q : ℕ) :
    unroll f N b (N * q) = b q := by
  have result := grid f N positive b step q 0 (Nat.zero_le N)
  simpa only [add_zero, Nat.sub_zero, step] using result

theorem one_step {X : Type*} (f : ℕ → X → X) (N : ℕ) (positive : 0 < N)
    (b : ℕ → X) (step : ∀ n, word (block f N n) N (b (n + 1)) = b n) (m : ℕ) :
    f m (unroll f N b (m + 1)) = unroll f N b m := by
  let q := m / N
  let r := m % N
  have remainder : r < N := Nat.mod_lt m positive
  have decomposition : N * q + r = m := Nat.div_add_mod m N
  have next : N * q + (r + 1) = m + 1 := by omega
  rw [← next, grid f N positive b step q (r + 1) (by omega),
    ← decomposition, grid f N positive b step q r remainder.le]
  have length : N - r = (N - (r + 1)) + 1 := by omega
  rw [length, word]
  change f (N * q + r) _ = block f N q (N - (r + 1)) _
  have time : N * (q + 1) - 1 - (N - (r + 1)) = N * q + r := by
    have expanded : N * (q + 1) = N * q + N := Nat.mul_succ N q
    omega
  rw [block, time]

theorem stays_in {X : Type*} (f : ℕ → X → X) (N : ℕ) (b : ℕ → X) (W : Set X)
    (inside : ∀ q j, j ≤ N → word (block f N q) j (b (q + 1)) ∈ W) (m : ℕ) :
    unroll f N b m ∈ W :=
  inside (m / N) (N - m % N) (Nat.sub_le _ _)

end LeanShared.BackwardBlockUnrolling
