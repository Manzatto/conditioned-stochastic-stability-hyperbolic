module
public import LeanShared.Dynamics.SeparatedOrbitSplitting

/-! Any actual Bowen-spanning family has weight comparable to the literal
separated partition sum. Injective nearest-center coding proves the bound;
no weighted-maximizer or spanning-partition comparison is assumed. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1600000 in
theorem partition_le_spanning_weight (T : X → X) (φ : X → ℝ) (n : ℕ)
    (ε D : ℝ) (positiveε : 0 < ε) (t : Finset X)
    (spans : ∀ x : X, ∃ y ∈ t, ∀ j < n, dist (T^[j] x) (T^[j] y) < ε)
    (bowen : ∀ x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    separatedPartitionSum T φ univ n (3 * ε) ≤
      ENNReal.ofReal (Real.exp D * ∑ y ∈ t, Real.exp (orbitSum T φ n y)) := by
  classical
  choose center member trace using spans
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun separated => ?_
  have injective : Set.InjOn center s := by
    intro x hx y hy equal
    by_contra different
    obtain ⟨j, hj, far⟩ := separated.2 x hx y hy different
    have first := trace x j hj
    have second := trace y j hj
    rw [← equal] at second
    have triangle := dist_triangle (T^[j] x) (T^[j] (center x)) (T^[j] y)
    rw [dist_comm (T^[j] (center x)) (T^[j] y)] at triangle
    linarith
  have pointBound (x : X) (_ : x ∈ s) : Real.exp (orbitSum T φ n x) ≤
      Real.exp D * Real.exp (orbitSum T φ n (center x)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (bowen x (center x) (trace x))).2])
  have upper := Finset.sum_le_sum_of_injOn
    (f := fun x => Real.exp (orbitSum T φ n x))
    (g := fun y => Real.exp D * Real.exp (orbitSum T φ n y)) center injective
    (fun y hy => by
      obtain ⟨x, _, equal⟩ := Finset.mem_image.mp hy
      exact equal ▸ member x)
    pointBound (fun _ _ _ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  rw [← Finset.mul_sum] at upper
  have enn := ENNReal.ofReal_le_ofReal upper
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)] at enn
  exact enn

end LeanShared.ThermodynamicDefinitions
