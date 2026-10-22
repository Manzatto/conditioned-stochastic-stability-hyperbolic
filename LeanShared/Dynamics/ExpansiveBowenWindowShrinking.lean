module
public import LeanShared.Dynamics.FiniteExpansiveCylinders
import all LeanShared.Dynamics.FiniteExpansiveTube

/-! A fixed two-sided buffer turns a coarse forward Bowen word into an
arbitrarily fine interior word. Its length is uniform over ALL horizons and
reference points, derived from actual compact expansivity. -/
public noncomputable section
open Set Function
namespace LeanShared.FiniteExpansiveWords
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_window_shrinking (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x y : X,
      (∀ i < n + 2 * N, dist (T^[i] x) (T^[i] y) ≤ c) →
      ∀ j < n, dist (T^[N + j] x) (T^[N + j] y) < ε := by
  obtain ⟨N, _, detects⟩ := FiniteExpansiveCylinders.exists_finite_separation T
    (isCompact_univ : IsCompact (univ : Set X)) c (fun x _ y _ => expansive x y) ε positiveε
  refine ⟨N, fun n x y close j hj => ?_⟩
  apply detects (T^[N + j] x) (T^[N + j] y)
  intro l hl
  refine ⟨mem_univ _, mem_univ _, ?_, mem_univ _, mem_univ _, ?_⟩
  · rw [← iterate_add_apply, ← iterate_add_apply]
    exact close (l + (N + j)) (by omega)
  · rw [backward_at_forward, backward_at_forward,
      ite_eq_left (show l ≤ N + j by omega), ite_eq_left (show l ≤ N + j by omega)]
    exact close (N + j - l) (by omega)

end LeanShared.FiniteExpansiveWords
