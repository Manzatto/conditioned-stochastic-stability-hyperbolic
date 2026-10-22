module
public import LeanShared.Dynamics.ExpansiveUniformTubeCardinality
public import LeanShared.Dynamics.SeparatedSpanningSubset
public import LeanShared.Dynamics.GibbsUpperEntropyEnergy

/-! An actual upper Gibbs estimate at one small radius extends to any
coarse radius below the expansivity/Bowen threshold. Uniform tube cardinality
constructs a finite fine-cylinder cover with horizon-independent size. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]

set_option maxHeartbeats 2400000 in
theorem upper_gibbs_scale_extension
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (δ ρ H D P : ℝ) (positiveδ : 0 < δ) (positiveρ : 0 < ρ)
    (positiveH : 0 < H) (coarse : 2 * ρ ≤ c)
    (ν : Measure X)
    (gibbs : ∀ n z U, IsOpen U →
      (∀ x ∈ U, ∀ j < n, dist (T^[j] x) (T^[j] z) < δ) →
      ν U ≤ ENNReal.ofReal (H * Real.exp (orbitSum T φ n z - (n : ℝ) * P)))
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 2 * ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    ∃ C > 0, ∀ n : ℕ, ∀ z : X,
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ} ≤
        ENNReal.ofReal (C * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) := by
  classical
  obtain ⟨K, tubeCount⟩ := FiniteExpansiveWords.exists_uniform_tube_card_bound
    T c positiveC expansive (δ / 2) (by positivity)
  refine ⟨((K + 1 : ℕ) : ℝ) * H * Real.exp D, by positivity, fun n z => ?_⟩
  let V := {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ}
  have count : ∀ s : Finset X, Separated T V n (δ / 2) s → s.card ≤ K := by
    intro s separated
    apply tubeCount n s ⟨fun _ _ => mem_univ _, separated.2⟩
    intro x hx y hy j hj
    have first := separated.1 x hx j hj
    have last := separated.1 y hy j hj
    have triangle := dist_triangle (T^[j] x) (T^[j] z) (T^[j] y)
    rw [dist_comm (T^[j] z) (T^[j] y)] at triangle
    linarith
  obtain ⟨s, separated, spanning⟩ := exists_separated_spanning_subset T V n (δ / 2)
    (by positivity) K count
  let U (y : X) := {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < δ}
  have openU (y : X) : IsOpen (U y) := by
    have opened := isOpen_biInter_finset (s := Finset.range n)
      (f := fun j => {x | dist (T^[j] x) (T^[j] y) < δ})
      (fun j _ => isOpen_lt ((T.continuous.iterate j).dist continuous_const) continuous_const)
    convert opened using 1
    ext x
    simp only [U, mem_ofPred_eq, mem_iInter, Finset.mem_range]
  have cover : V ⊆ ⋃ y ∈ s, U y := by
    intro x hx
    obtain ⟨y, hy, near⟩ := spanning x hx
    refine mem_iUnion₂.mpr ⟨y, hy, fun j hj => ?_⟩
    exact (near j hj).trans (by linarith)
  have individual (y : X) (hy : y ∈ s) : ν (U y) ≤
      ENNReal.ofReal (H * Real.exp D * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) := by
    have energy := (abs_le.mp (bowen n y z (fun j hj =>
      (separated.1 y hy j hj).trans_lt (by linarith)))).2
    have exponential : Real.exp (orbitSum T φ n y - (n : ℝ) * P) ≤
        Real.exp D * Real.exp (orbitSum T φ n z - (n : ℝ) * P) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    apply (gibbs n y (U y) (openU y) (fun _ hx => hx)).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left exponential positiveH.le
  have size : s.card ≤ K + 1 := (count s separated).trans (Nat.le_succ K)
  calc
    ν V ≤ ν (⋃ y ∈ s, U y) := measure_mono cover
    _ ≤ ∑ y ∈ s, ν (U y) := measure_biUnion_finset_le s U
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal (H * Real.exp D * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) :=
      Finset.sum_le_sum individual
    _ = ENNReal.ofReal ((s.card : ℝ) *
        (H * Real.exp D * Real.exp (orbitSum T φ n z - (n : ℝ) * P))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((K + 1 : ℕ) : ℝ) *
        (H * Real.exp D * Real.exp (orbitSum T φ n z - (n : ℝ) * P))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast size) (by positivity)
    _ = _ := by congr 1; ring

end LeanShared.ThermodynamicDefinitions
