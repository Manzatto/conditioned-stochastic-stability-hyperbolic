module
public import LeanShared.Dynamics.PointSpecificationThreeSegments
public import LeanShared.Dynamics.ThreeSegmentOrbitEnergy
public import LeanShared.Dynamics.WeightedSeparatedOrbitGluing
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Actual three-piece specification constructs a separated weighted family
inside a prescribed middle Bowen cylinder. Both independent endpoint words
and the same chosen tracing points are retained in the lower estimate. -/
public noncomputable section
open Set
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 2000000 in
theorem prescribed_middle_weighted_gluing
    (T : X → X) (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (gap : ℕ) (positiveGap : 0 < gap)
    (tracing : ∀ n k m : ℕ, ∀ x z y : X, ∃ w : X,
      (∀ j ≤ n, dist (T^[j] w) (T^[j] x) < ε) ∧
      (∀ j ≤ k, dist (T^[n + gap + j] w) (T^[j] z) < ε) ∧
      ∀ j ≤ m, dist (T^[n + gap + k + gap + j] w) (T^[j] y) < ε)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D)
    (n k m : ℕ) (z : X) (s t : Finset X)
    (first : Separated T univ (n + 1) (3 * ε) s)
    (last : Separated T univ (m + 1) (3 * ε) t) :
    ∃ q : Finset X, Separated T univ (n + gap + k + gap + m + 1) ε q ∧
      (∀ w ∈ q, ∀ j ≤ k, dist (T^[n + gap + j] w) (T^[j] z) < ε) ∧
      Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
        (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
        (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) ≤
          ∑ w ∈ q, Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w) := by
  classical
  let I := {p : X × X // p ∈ s.product t}
  choose trace traceFirst traceMiddle traceLast using
    (fun p : I => tracing n k m p.val.1 z p.val.2)
  have separates := traced_pair_separation T univ s t n m (gap + k + gap) ε first last trace
    traceFirst (fun p j hj => by simpa only [Nat.add_assoc] using traceLast p j hj)
  have injective : Function.Injective trace := by
    intro p q equal
    by_contra different
    obtain ⟨j, _, apart⟩ := separates p q different
    rw [equal, dist_self] at apart
    exact (not_le_of_gt positiveε) apart
  let q := Finset.univ.image trace
  have weightBound (p : I) :
      Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
        Real.exp (orbitSum T φ (n + 1) p.val.1) * Real.exp (orbitSum T φ (m + 1) p.val.2) ≤
      Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) (trace p)) := by
    have energy := orbitSum_three_gluing_lower T φ univ (fun _ _ => mem_univ _) ‖φ‖
      (fun x _ => (abs_le.mp (by simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm x)).1)
      n k m gap positiveGap p.val.1 z p.val.2 (trace p) (mem_univ _) D
      (bowen (n + 1) _ _ (fun j hj => traceFirst p j (by omega)))
      (bowen (k + 1) _ _ (fun j hj => by
        rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap)]
        exact traceMiddle p j (by omega)))
      (bowen (m + 1) _ _ (fun j hj => by
        rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap + k + gap)]
        exact traceLast p j (by omega)))
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨q, ⟨fun _ _ => mem_univ _, ?_⟩, ?_, ?_⟩
  · intro x hx y hy different
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, far⟩ := separates p r (fun equal => different (congrArg trace equal))
    exact ⟨j, by omega, far⟩
  · intro w hw
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
    exact traceMiddle p
  · have productSum : (∑ p : I,
        Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
          Real.exp (orbitSum T φ (n + 1) p.val.1) * Real.exp (orbitSum T φ (m + 1) p.val.2)) =
        Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
          (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) := by
      rw [Finset.sum_coe_sort (s.product t)
        (fun p : X × X => Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
          Real.exp (orbitSum T φ (n + 1) p.1) * Real.exp (orbitSum T φ (m + 1) p.2)),
        Finset.product_eq_sprod, Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [← productSum]
    change _ ≤ ∑ w ∈ Finset.univ.image trace, _
    rw [Finset.sum_image (fun _ _ _ _ equal => injective equal)]
    exact Finset.sum_le_sum (fun p _ => weightBound p)

end LeanShared.ThermodynamicDefinitions
