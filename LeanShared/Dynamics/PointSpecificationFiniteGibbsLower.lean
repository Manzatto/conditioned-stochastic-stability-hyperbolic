module
public import LeanShared.Dynamics.FiniteGibbsSpecificationLower
public import LeanShared.Dynamics.PointSpecificationPartitionBounds
public import LeanShared.Dynamics.FiniteGibbsCylinderNormalization

/-! Actual compact specification and Bowen distortion yield a uniform
positive lower Gibbs-cylinder bound. Prefix/suffix partition approximants,
their actual pressure, seam losses and probability normalization are proved
internally; no Gibbs lower bound or partition normalization is a source. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions

private theorem seam_identity (S n k m g D J A B P : ℝ) (positiveB : 0 < B) :
    (Real.exp (-4 * D - 2 * g * (J + P)) * A ^ 2 / B * Real.exp (S - k * P)) *
      (B * Real.exp ((n + k + m + 2 * g) * P)) =
    Real.exp (S - 4 * D - 2 * g * J) * (A * Real.exp (n * P)) * (A * Real.exp (m * P)) := by
  have exponents : -4 * D - 2 * g * (J + P) + (S - k * P) +
      (n + k + m + 2 * g) * P = S - 4 * D - 2 * g * J + n * P + m * P := by ring
  have exponential : Real.exp (-4 * D - 2 * g * (J + P)) * Real.exp (S - k * P) *
      Real.exp ((n + k + m + 2 * g) * P) =
      Real.exp (S - 4 * D - 2 * g * J) * Real.exp (n * P) * Real.exp (m * P) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, exponents]
  calc
    _ = A ^ 2 * (Real.exp (-4 * D - 2 * g * (J + P)) * Real.exp (S - k * P) *
        Real.exp ((n + k + m + 2 * g) * P)) := by field_simp
    _ = _ := by rw [exponential]; ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 3200000 in
theorem normalized_finite_gibbs_lower_of_point_specification
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 18 * ε ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 9 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ gap : ℕ, 0 < gap ∧ ∃ H > 0,
      ∀ n k m : ℕ, ∀ z : X, ∀ a : Finset X, ∀ ha : a.Nonempty,
        Separated T univ (n + gap + k + gap + m + 1) ε a →
        (∀ x : X, ∃ y ∈ a, ∀ j < n + gap + k + gap + m + 1,
          dist (T^[j] x) (T^[j] y) < ε) →
        ∀ U : Set X, MeasurableSet U →
          (∀ w, (∀ j < k + 1, dist (T^[n + gap + j] w) (T^[j] z) < 4 * ε) → w ∈ U) →
          let : Nonempty a := ha.to_subtype
          ENNReal.ofReal (H * Real.exp (orbitSum T φ (k + 1) z - ((k + 1 : ℕ) : ℝ) * P)) ≤
            (FiniteAtomicProbability.gibbs
              (fun w : a => orbitSum T φ (n + gap + k + gap + m + 1) w.val)
              Subtype.val : Measure X) U := by
  classical
  obtain ⟨P, pressureP, A, positiveA, _, _, normalization⟩ :=
    partition_bounds_of_point_specification T c₀ positive₀ expansive φ (3 * ε) D
      (by positivity) (by linarith)
      (fun h x y close => bowen h x y (fun j hj => by have near := close j hj; linarith)) specification
  have scale9 : 3 * (3 * ε) = 9 * ε := by ring
  simp only [scale9] at normalization
  obtain ⟨Q, pressureQ, B, positiveB, upper⟩ := partition_upper_of_point_specification
    T c₀ positive₀ expansive φ (ε / 3) D (by positivity) (by linarith)
      (fun h x y close => bowen h x y (fun j hj => by have near := close j hj; linarith)) specification
  have same : Q = P := EReal.coe_injective (pressureQ.symm.trans pressureP)
  subst Q
  have scaleε : 3 * (ε / 3) = ε := by ring
  simp only [scaleε] at upper
  obtain ⟨gap, positiveGap, probabilityLower⟩ := finite_gibbs_specification_cylinder_lower T φ ε D positiveε
    specification (fun h x y close => bowen h x y (fun j hj => (close j hj).trans_le (by linarith)))
  let H := Real.exp (-4 * D - 2 * (gap - 1 : ℕ) * (‖φ‖ + P)) * (A / 2) ^ 2 / B
  have positiveH : 0 < H := div_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos (by positivity))) positiveB
  obtain ⟨alphabet, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c₀ positive₀ expansive
  obtain ⟨p9, count9⟩ := counts (9 * ε) (by positivity)
  obtain ⟨pε, countε⟩ := counts ε positiveε
  have finite9 (N : ℕ) := partitionSum_positive_finite_of_count T φ N p9 alphabet (9 * ε) (count9 N)
  have finiteε (N : ℕ) := partitionSum_positive_finite_of_count T φ N pε alphabet ε (countε N)
  refine ⟨P, pressureP, gap, positiveGap, H, positiveH, ?_⟩
  intro n k m z a ha separated spans U measurable contains
  let : Nonempty a := ha.to_subtype
  dsimp only
  obtain ⟨s, _, first, lowerS, _⟩ := exists_separated_half_sum T φ univ (n + 1) (9 * ε)
    (finite9 _).1 (finite9 _).2
  obtain ⟨t, _, last, lowerT, _⟩ := exists_separated_half_sum T φ univ (m + 1) (9 * ε)
    (finite9 _).1 (finite9 _).2
  have firstLower : (A / 2) * Real.exp (((n + 1 : ℕ) : ℝ) * P) ≤
      ∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x) := by
    have bound := div_le_div_of_nonneg_right (normalization (n + 1) (by omega)).1 (by norm_num : (0 : ℝ) ≤ 2)
    exact (by convert bound.trans lowerS.le using 1; ring)
  have lastLower : (A / 2) * Real.exp (((m + 1 : ℕ) : ℝ) * P) ≤
      ∑ x ∈ t, Real.exp (orbitSum T φ (m + 1) x) := by
    have bound := div_le_div_of_nonneg_right (normalization (m + 1) (by omega)).1 (by norm_num : (0 : ℝ) ≤ 2)
    exact (by convert bound.trans lowerT.le using 1; ring)
  let N := n + gap + k + gap + m + 1
  let W := ∑ w ∈ a, Real.exp (orbitSum T φ N w)
  have positiveW : 0 < W := Finset.sum_pos (fun _ _ => Real.exp_pos _) ha
  have upperW : W ≤ B * Real.exp ((N : ℝ) * P) := by
    have below : (∑ w ∈ a, ENNReal.ofReal (Real.exp (orbitSum T φ N w))) ≤
        separatedPartitionSum T φ univ N ε := by
      unfold separatedPartitionSum
      exact le_iSup_of_le a (le_iSup_of_le separated le_rfl)
    have realBelow := ENNReal.toReal_mono (finiteε N).2 below
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at realBelow
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at realBelow
    exact realBelow.trans (upper N (by dsimp [N]; omega))
  have size : (N : ℝ) = ((n + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) +
      ((m + 1 : ℕ) : ℝ) + 2 * ((gap - 1 : ℕ) : ℝ) := by
    have equality : N = (n + 1) + (k + 1) + (m + 1) + 2 * (gap - 1) := by dsimp [N]; omega
    exact_mod_cast equality
  have identity := seam_identity (orbitSum T φ (k + 1) z) ((n + 1 : ℕ) : ℝ)
    ((k + 1 : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) ((gap - 1 : ℕ) : ℝ) D ‖φ‖ (A / 2) B P positiveB
  rw [← size] at identity
  have weighted : (H * Real.exp (orbitSum T φ (k + 1) z - ((k + 1 : ℕ) : ℝ) * P)) * W ≤
      Real.exp (orbitSum T φ (k + 1) z - 4 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
        (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
        (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) := by
    calc
      _ ≤ (H * Real.exp (orbitSum T φ (k + 1) z - ((k + 1 : ℕ) : ℝ) * P)) *
          (B * Real.exp ((N : ℝ) * P)) := mul_le_mul_of_nonneg_left upperW (by positivity)
      _ = _ := identity
      _ ≤ _ := by gcongr
  have normalized := (le_div_iff₀ positiveW).mpr weighted
  have lower := probabilityLower n k m z s t a ha first last spans U measurable contains
  exact (ENNReal.ofReal_le_ofReal normalized).trans lower

end LeanShared.ThermodynamicDefinitions
