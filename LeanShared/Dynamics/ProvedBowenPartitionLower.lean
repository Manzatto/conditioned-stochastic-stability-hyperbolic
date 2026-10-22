module

public import LeanShared.Dynamics.BowenPartitionSubmultiplication
public import LeanShared.Dynamics.BowenFixedScalePressure
public import LeanShared.Dynamics.SubmultiplicativePartitionLower
public import LeanShared.Dynamics.SeparatedPartitionFiniteness
public import LeanShared.Dynamics.ExpansiveFinitePressure

/-! Compact expansivity and actual Bowen distortion give a uniform
exponential lower partition bound at the literal pressure. Actual finite
spanning, submultiplicativity and Fekete estimates are derived internally. -/
public noncomputable section
open Set Filter
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2000000 in
theorem partition_lower_at_pressure (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 6 * ε ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ B > 0,
      ∀ n : ℕ, 0 < n → B * Real.exp ((n : ℝ) * P) ≤
        (separatedPartitionSum T φ univ n (3 * ε)).toReal := by
  obtain ⟨P, pressureP⟩ := finite_pressure_of_expansive T c positiveC expansive φ φ.continuous
  obtain ⟨C, positive, multiplication⟩ := partition_submultiplication
    T c positiveC expansive φ ε D positiveε coarse bowen
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts (3 * ε) (by positivity)
  have finite (n : ℕ) := partitionSum_positive_finite_of_count T φ n p a (3 * ε) (count n)
  let Z := fun n => (separatedPartitionSum T φ univ n (3 * ε)).toReal
  have positiveZ (n : ℕ) : 0 < Z n := ENNReal.toReal_pos (finite n).1 (finite n).2
  have product (n m : ℕ) : Z (n + m) ≤ C * Z n * Z m := by
    have comparison := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite n).2) (finite m).2)
      (multiplication n m)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal positive.le, Z] using comparison
  have same : (fun n : ℕ => ((Real.log (Z n) / (n : ℝ) : ℝ) : EReal)) =ᶠ[atTop]
      (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        (separatedPartitionSum T φ univ n (3 * ε)).log) := by
    filter_upwards [eventually_gt_atTop 0] with n _
    rw [ENNReal.log_pos_real (finite n).1 (finite n).2, ← EReal.coe_mul]
    congr 1
    dsimp only [Z]
    ring
  have limiting : limsup (fun n : ℕ => ((Real.log (Z n) / (n : ℝ) : ℝ) : EReal)) atTop = (P : EReal) :=
    (limsup_congr same).trans ((pressure_at_bowen_scale T c positiveC expansive φ (3 * ε) D
      (by positivity) (by linarith) bowen).symm.trans pressureP)
  have bound := SubmultiplicativePartitionLower.lower_bound Z positiveZ C positive P product limiting
  refine ⟨P, pressureP, 1 / C, div_pos zero_lt_one positive, fun n hn => ?_⟩
  calc
    _ = Real.exp ((n : ℝ) * P) / C := by ring
    _ ≤ _ := bound n hn

end LeanShared.ThermodynamicDefinitions
