module

public import LeanShared.Dynamics.ExpansiveUniformTubeCardinality
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality
public import LeanShared.Dynamics.SeparatedSpanningSet
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Expansivity and Bowen distortion compare all finer weighted separated
sums with one actual coarse separated spanning sum, by a constant independent
of the horizon. The bounded fiber cardinality is derived from expansivity. -/
public noncomputable section
open Set Function
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2400000 in
theorem separated_scale_comparison (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ρ D : ℝ) (positiveρ : 0 < ρ) (coarse : 2 * ρ ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ, ∃ t : Finset X, Separated T univ n ρ t ∧
      ∀ s : Finset X, Separated T univ n ε s →
        (∑ x ∈ s, Real.exp (orbitSum T φ n x)) ≤
          C * ∑ y ∈ t, Real.exp (orbitSum T φ n y) := by
  classical
  obtain ⟨K, tubeCount⟩ := FiniteExpansiveWords.exists_uniform_tube_card_bound
    T c positiveC expansive ε positiveε
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts ρ positiveρ
  refine ⟨((K + 1 : ℕ) : ℝ) * Real.exp D, mul_pos (by positivity) (Real.exp_pos _), ?_⟩
  intro n
  obtain ⟨t, _, separated, spanning⟩ := exists_separated_spanning T n ρ positiveρ
    (a ^ (n + p)) (count n)
  choose center member near using spanning
  refine ⟨t, separated, fun s fine => ?_⟩
  let weight := fun x => Real.exp (orbitSum T φ n x)
  have individual (x : X) : weight x ≤ Real.exp D * weight (center x) := by
    have energy := (abs_le.mp (bowen n x (center x) (near x))).2
    have scaled := Real.exp_le_exp.mpr energy
    rw [Real.exp_sub] at scaled
    exact (div_le_iff₀ (Real.exp_pos _)).mp scaled
  have fibers (y : X) : (s.filter (fun x => center x = y)).card ≤ K := by
    apply tubeCount n _
    · refine ⟨fun _ _ => mem_univ _, ?_⟩
      intro x hx z hz different
      exact fine.2 x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 different
    · intro x hx z hz j hj
      have first := near x j hj
      have second := near z j hj
      rw [(Finset.mem_filter.mp hx).2] at first
      rw [(Finset.mem_filter.mp hz).2] at second
      have triangle := dist_triangle (T^[j] x) (T^[j] y) (T^[j] z)
      rw [dist_comm (T^[j] y) (T^[j] z)] at triangle
      linarith
  have maps : ∀ x ∈ s, center x ∈ t := fun x _ => member x
  rw [← Finset.sum_fiberwise_of_maps_to maps weight]
  calc
    _ ≤ ∑ y ∈ t, ((K + 1 : ℕ) : ℝ) * (Real.exp D * weight y) := by
      apply Finset.sum_le_sum
      intro y _
      calc
        _ ≤ ∑ _x ∈ s.filter (fun x => center x = y), Real.exp D * weight y :=
          Finset.sum_le_sum (fun x hx => by simpa only [(Finset.mem_filter.mp hx).2] using individual x)
        _ = ((s.filter (fun x => center x = y)).card : ℝ) * (Real.exp D * weight y) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (fibers y).trans (Nat.le_succ K))
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = _ := by simp only [← mul_assoc, ← Finset.mul_sum, weight]

end LeanShared.ThermodynamicDefinitions
