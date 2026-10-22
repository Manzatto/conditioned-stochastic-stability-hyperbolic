module

public import LeanShared.Dynamics.WeightedTracedPairsInside

/-! The same tracing points supplied by specification carry a quantitative
Gibbs mass lower bound in their prescribed orbit-cylinder neighbourhoods.
Finite separated packing converts the actual product orbit weights into
measure; no mass-correlation assumption is introduced. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

set_option maxHeartbeats 800000 in
theorem gibbs_traced_pair_mass (T : X → X) (φ : X → ℝ) (ν : Measure X)
    (s t : Finset X) (n m gap : ℕ) (ε A P a : ℝ)
    (positive : 0 < ε) (nonnegative : 0 ≤ A)
    (first : Separated T univ (n + 1) (9 * ε) s)
    (second : Separated T univ (m + 1) (9 * ε) t)
    (trace : {p : X × X // p ∈ s.product t} → X)
    (traceFirst : ∀ p, ∀ j ≤ n, dist (T^[j] (trace p)) (T^[j] p.val.1) < 3 * ε)
    (traceSecond : ∀ p, ∀ j ≤ m,
      dist (T^[n + gap + j] (trace p)) (T^[j] p.val.2) < 3 * ε)
    (weightBound : ∀ p,
      a * Real.exp (orbitSum T φ (n + 1) p.val.1) *
        Real.exp (orbitSum T φ (m + 1) p.val.2) ≤
      Real.exp (orbitSum T φ (n + gap + m + 1) (trace p)))
    (U : Set X)
    (measurable : ∀ y : X, MeasurableSet
      {x | ∀ j < n + gap + m + 1, dist (T^[j] x) (T^[j] y) < ε})
    (inside : ∀ p, {x | ∀ j < n + gap + m + 1,
      dist (T^[j] x) (T^[j] (trace p)) < ε} ⊆ U)
    (lower : ∀ y : X, ENNReal.ofReal
      (A * Real.exp (orbitSum T φ (n + gap + m + 1) y -
        (n + gap + m + 1 : ℕ) * P)) ≤
      ν {x | ∀ j < n + gap + m + 1, dist (T^[j] x) (T^[j] y) < ε}) :
    ENNReal.ofReal (A * Real.exp (-((n + gap + m + 1 : ℕ) : ℝ) * P) *
      (a * (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
        (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)))) ≤ ν U := by
  classical
  let N := n + gap + m + 1
  obtain ⟨q, contained, separated, weights⟩ := weighted_traced_pairs_inside T univ
    s t n m gap (3 * ε) (by positivity)
    (by convert first using 1; ring) (by convert second using 1; ring)
    trace (fun _ => mem_univ _) traceFirst traceSecond
    {y | {x | ∀ j < N, dist (T^[j] x) (T^[j] y) < ε} ⊆ U} inside
    (fun x => Real.exp (orbitSum T φ N x))
    (fun x => Real.exp (orbitSum T φ (n + 1) x))
    (fun y => Real.exp (orbitSum T φ (m + 1) y)) a weightBound
  have fineSeparated : Separated T univ N (2 * ε) q := by
    refine ⟨separated.1, fun x hx y hy different => ?_⟩
    obtain ⟨j, hj, apart⟩ := separated.2 x hx y hy different
    exact ⟨j, hj, by linarith⟩
  have packing := gibbs_packing_weight T φ ν univ U q N ε A P fineSeparated
    (fun y _ => measurable y) (fun y hy => contained hy) (fun y _ => lower y)
  have sumIdentity : (∑ y ∈ q, ENNReal.ofReal
      (A * Real.exp (orbitSum T φ N y - (N : ℝ) * P))) =
      ENNReal.ofReal (A * Real.exp (-(N : ℝ) * P) *
        ∑ y ∈ q, Real.exp (orbitSum T φ N y)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg nonnegative (Real.exp_nonneg _))]
    congr 1
    have negEq : -((N : ℝ) * P) = -(N : ℝ) * P := by ring
    simp_rw [sub_eq_add_neg, Real.exp_add, negEq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [sumIdentity] at packing
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) packing
  exact mul_le_mul_of_nonneg_left weights (mul_nonneg nonnegative (Real.exp_nonneg _))

end LeanShared.ThermodynamicDefinitions
