module
public import LeanShared.Dynamics.BowenCylinderPartitionBound
public import LeanShared.Dynamics.FiniteGibbsCylinderMass

/-! Upper bounds on literal measurable cylinders for the actual finite
Gibbs probabilities. All prefix/suffix coding and their partition bounds
are constructed; no Gibbs property is assumed. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 1600000 in
theorem finite_gibbs_cylinder_bound (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D)
    (n k m : ℕ) (z : X) (s : Finset X) (nonempty : s.Nonempty)
    (separated : Separated T univ (n + k + m) (3 * ε) s)
    (U : Set X) (measurable : MeasurableSet U)
    (inside : ∀ x ∈ U, ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε) :
    let : Nonempty s := nonempty.to_subtype
    (FiniteAtomicProbability.gibbs (fun x : s => orbitSum T φ (n + k + m) x.val)
      Subtype.val : Measure X) U ≤
      (ENNReal.ofReal (Real.exp (3 * D + orbitSum T φ k z)) *
        separatedPartitionSum T φ univ n ε * separatedPartitionSum T φ univ m ε) /
          ENNReal.ofReal (∑ x ∈ s, Real.exp (orbitSum T φ (n + k + m) x)) := by
  classical
  let : Nonempty s := nonempty.to_subtype
  dsimp only
  have mass := FiniteAtomicProbability.gibbs_apply
    (fun x : s => orbitSum T φ (n + k + m) x.val) Subtype.val U measurable
  have numerator : (∑ i ∈ Finset.univ.filter (fun i : s => i.val ∈ U),
      Real.exp (orbitSum T φ (n + k + m) i.val)) =
      ∑ x ∈ s.filter (fun x => x ∈ U), Real.exp (orbitSum T φ (n + k + m) x) := by
    simpa only [Finset.sum_filter] using Finset.sum_coe_sort s
      (fun x => if x ∈ U then Real.exp (orbitSum T φ (n + k + m) x) else 0)
  have denominator : FiniteGibbsOptimizer.partition
      (fun x : s => orbitSum T φ (n + k + m) x.val) =
      ∑ x ∈ s, Real.exp (orbitSum T φ (n + k + m) x) :=
    Finset.sum_coe_sort s (fun x => Real.exp (orbitSum T φ (n + k + m) x))
  have positive : 0 < ∑ x ∈ s, Real.exp (orbitSum T φ (n + k + m) x) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) nonempty
  rw [numerator, denominator, ENNReal.ofReal_div_of_pos positive] at mass
  rw [mass]
  have subset : s.filter (fun x => x ∈ U) ⊆
      s.filter (fun x => ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε) := by
    intro x hx
    obtain ⟨hs, hU⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hs, inside x hU⟩
  have numeratorBound := (Finset.sum_le_sum_of_subset subset
    (f := fun x => ENNReal.ofReal (Real.exp (orbitSum T φ (n + k + m) x)))).trans
      (cylinder_partition_bound T c positiveC expansive φ ε D positiveε bowen n k m z s separated)
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  gcongr

end LeanShared.ThermodynamicDefinitions
