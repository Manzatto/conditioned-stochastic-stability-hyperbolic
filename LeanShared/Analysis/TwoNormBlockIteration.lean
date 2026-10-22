module

public import LeanShared.Analysis.UniformWordGrowth
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Uniform two-norm bounds from a robust finite block estimate

Only one fixed block length needs a contracting strong coefficient. Its
weak error is retained and summed, rather than requiring contraction of the
ordinary strong operator norm (which may contain a leading eigenvalue).
This is the iteration step.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanShared.TwoNormBlockIteration

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A uniform finite-block Lasota–Yorke inequality implies the full arbitrary
word inequality. The remainder constant and accumulated weak error are
explicit. No continuity in strong operator norm is assumed. -/
theorem uniform_twoNorm_bound
    (P : List G → E →L[𝕜] E) (ι : E →L[𝕜] F)
    (happend : ∀ u v x, P (u ++ v) x = P u (P v x))
    (N : ℕ) (hN : 0 < N) (ρ C₀ M L b Cw : ℝ)
    (hρ : 0 < ρ) (hρC₀ : ρ < C₀) (hM : 0 ≤ M) (hMC₀ : M ≤ C₀)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (hCw : 0 ≤ Cw)
    (hshort : ∀ word : List G, word.length < N → ∀ x,
      ‖P word x‖ ≤ L ^ word.length * ‖x‖)
    (hweak : ∀ word : List G, ∀ x,
      ‖ι (P word x)‖ ≤ Cw * M ^ word.length * ‖ι x‖)
    (hblock : ∀ word : List G, word.length = N → ∀ x,
      ‖P word x‖ ≤ ρ ^ N * ‖x‖ + b * ‖ι x‖) :
    let C := ∑ r ∈ Finset.range N, (L / ρ) ^ r
    let D := b * Cw / (C₀ ^ N - ρ ^ N)
    0 ≤ C ∧ 0 ≤ D ∧ ∀ word : List G, ∀ x,
      ‖P word x‖ ≤ C * ρ ^ word.length * ‖x‖ + D * C₀ ^ word.length * ‖ι x‖ := by
  let C := ∑ r ∈ Finset.range N, (L / ρ) ^ r
  let D := b * Cw / (C₀ ^ N - ρ ^ N)
  have hC₀ : 0 < C₀ := hρ.trans hρC₀
  have hgap : 0 < C₀ ^ N - ρ ^ N := by
    exact sub_pos.mpr (pow_lt_pow_left₀ hρC₀ hρ.le hN.ne')
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => pow_nonneg (div_nonneg hL hρ.le) _
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hb hCw) hgap.le
  have hDrec : ρ ^ N * D + b * Cw = D * C₀ ^ N := by
    have he : D * (C₀ ^ N - ρ ^ N) = b * Cw := div_mul_cancel₀ _ hgap.ne'
    nlinarith [he]
  refine ⟨hC, hD, ?_⟩
  suffices ∀ n : ℕ, ∀ word : List G, word.length = n → ∀ x,
      ‖P word x‖ ≤ C * ρ ^ word.length * ‖x‖ + D * C₀ ^ word.length * ‖ι x‖ by
    exact fun word => this word.length word rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro word hlen x
    by_cases hn : n < N
    · have hterm : (L / ρ) ^ word.length ≤ C := by
        apply Finset.single_le_sum (fun r _ => pow_nonneg (div_nonneg hL hρ.le) r)
        exact Finset.mem_range.mpr (hlen ▸ hn)
      calc
        ‖P word x‖ ≤ L ^ word.length * ‖x‖ := hshort word (hlen ▸ hn) x
        _ = (L / ρ) ^ word.length * ρ ^ word.length * ‖x‖ := by
          rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ.ne')]
        _ ≤ C * ρ ^ word.length * ‖x‖ := by gcongr
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hNn : N ≤ word.length := hlen ▸ Nat.le_of_not_gt hn
      have htake : (word.take N).length = N := by simp [List.length_take, Nat.min_eq_left hNn]
      have hdrop : (word.drop N).length < n := by simp only [List.length_drop]; omega
      have hi := ih _ hdrop (word.drop N) rfl x
      have hw := hweak (word.drop N) x
      have hpow : M ^ (word.drop N).length ≤ C₀ ^ (word.drop N).length :=
        pow_le_pow_left₀ hM hMC₀ _
      have hlen' : N + (word.drop N).length = word.length := by
        simp only [List.length_drop, Nat.add_sub_of_le hNn]
      calc
        ‖P word x‖ = ‖P (word.take N) (P (word.drop N) x)‖ := by
          rw [← happend, List.take_append_drop]
        _ ≤ ρ ^ N * ‖P (word.drop N) x‖ + b * ‖ι (P (word.drop N) x)‖ :=
          hblock _ htake _
        _ ≤ ρ ^ N * (C * ρ ^ (word.drop N).length * ‖x‖ +
            D * C₀ ^ (word.drop N).length * ‖ι x‖) +
            b * (Cw * M ^ (word.drop N).length * ‖ι x‖) := by gcongr
        _ ≤ ρ ^ N * (C * ρ ^ (word.drop N).length * ‖x‖ +
            D * C₀ ^ (word.drop N).length * ‖ι x‖) +
            b * (Cw * C₀ ^ (word.drop N).length * ‖ι x‖) := by gcongr
        _ = C * (ρ ^ N * ρ ^ (word.drop N).length) * ‖x‖ +
            (ρ ^ N * D + b * Cw) * C₀ ^ (word.drop N).length * ‖ι x‖ := by ring
        _ = _ := by rw [hDrec, mul_assoc D, ← pow_add, ← pow_add, hlen']

end LeanShared.TwoNormBlockIteration
