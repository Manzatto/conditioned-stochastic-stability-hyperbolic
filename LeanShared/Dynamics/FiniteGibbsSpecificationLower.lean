module
public import LeanShared.Dynamics.SpecificationCylinderWeightLower
public import LeanShared.Dynamics.FiniteGibbsCylinderMass

/-! Actual lower probabilities of prescribed-middle cylinders for the
constructed finite Gibbs law, from specification and an actual spanning
orbit family. No Gibbs-cylinder mass is supplied as a hypothesis. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

set_option maxHeartbeats 2400000 in
theorem finite_gibbs_specification_cylinder_lower
    (T : X → X) (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n k m : ℕ, ∀ z : X, ∀ s t a : Finset X,
      ∀ ha : a.Nonempty,
      Separated T univ (n + 1) (9 * ε) s →
      Separated T univ (m + 1) (9 * ε) t →
      (∀ x : X, ∃ y ∈ a, ∀ j < n + gap + k + gap + m + 1,
        dist (T^[j] x) (T^[j] y) < ε) →
      ∀ U : Set X, MeasurableSet U →
        (∀ w, (∀ j < k + 1, dist (T^[n + gap + j] w) (T^[j] z) < 4 * ε) → w ∈ U) →
        let : Nonempty a := ha.to_subtype
        ENNReal.ofReal
          ((Real.exp (orbitSum T φ (k + 1) z - 4 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
            (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
            (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y))) /
              (∑ w ∈ a, Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w))) ≤
          (FiniteAtomicProbability.gibbs
            (fun w : a => orbitSum T φ (n + gap + k + gap + m + 1) w.val)
            Subtype.val : Measure X) U := by
  classical
  obtain ⟨gap, positiveGap, lower⟩ := specification_cylinder_weight_lower
    T φ ε D positiveε specification bowen
  refine ⟨gap, positiveGap, fun n k m z s t a ha first last spans U measurable contains => ?_⟩
  let : Nonempty a := ha.to_subtype
  dsimp only
  have weighted := lower n k m z s t a first last spans
  have subset : a.filter (fun w => ∀ j < k + 1,
      dist (T^[n + gap + j] w) (T^[j] z) < 4 * ε) ⊆ a.filter (fun w => w ∈ U) := by
    intro w hw
    obtain ⟨member, near⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨member, contains w near⟩
  have numeratorBound := weighted.trans (Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun _ _ _ => Real.exp_nonneg _))
  have mass := FiniteAtomicProbability.gibbs_apply
    (fun w : a => orbitSum T φ (n + gap + k + gap + m + 1) w.val) Subtype.val U measurable
  have numerator : (∑ i ∈ Finset.univ.filter (fun i : a => i.val ∈ U),
      Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) i.val)) =
      ∑ w ∈ a.filter (fun w => w ∈ U), Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w) := by
    simpa only [Finset.sum_filter] using Finset.sum_coe_sort a
      (fun w => if w ∈ U then Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w) else 0)
  have denominator : FiniteGibbsOptimizer.partition
      (fun w : a => orbitSum T φ (n + gap + k + gap + m + 1) w.val) =
      ∑ w ∈ a, Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w) :=
    Finset.sum_coe_sort a (fun w => Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w))
  rw [mass, numerator, denominator]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right numeratorBound
    (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)))

end LeanShared.ThermodynamicDefinitions
