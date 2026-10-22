module

public import LeanShared.Dynamics.BowenEntropyEnergyEstimate
public import LeanShared.Dynamics.ExpansiveFinitePressure
public import LeanShared.Dynamics.ExpansiveGeneratorEntropy
public import LeanShared.Dynamics.ExpansiveNullBoundaryGenerator

/-! The actual entropy and invariant potential integral are bounded by
literal weighted separated-set pressure. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

theorem MeasurablePartition.free_energy_le_pressure (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (φ : X →ᵇ ℝ) :
    ((P.entropyRate T (μ : Measure X) + ∫ x, φ x ∂(μ : Measure X) : ℝ) : EReal) ≤
      pressure T φ univ := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  obtain ⟨Pr,pressurePr⟩ := finite_pressure_of_expansive T c positive expansive φ φ.continuous
  have slack (η : ℝ) (ηpositive : 0 < η) :
      P.entropyRate T (μ : Measure X) + (∫ x, φ x ∂(μ : Measure X)) - 2*η ≤ Pr := by
    obtain ⟨ε,εpositive,bound⟩ := P.exists_bowen_entropy_energy_bound T c positive expansive μ invariant φ η ηpositive
    obtain ⟨a,_,counts⟩ := LeanShared.FiniteExpansiveWords.exists_uniform_card_bound T c positive expansive
    obtain ⟨p,count⟩ := counts ε εpositive
    have compare : ∀ᶠ n : ℕ in atTop,
        ((dynamicalEntropy P T (μ : Measure X) n/n + (∫ x, φ x ∂(μ : Measure X)) - 2*η : ℝ) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ univ n ε).log := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      obtain ⟨nonzero,finite⟩ := partitionSum_positive_finite_of_count T φ n p a ε (count n)
      have identity : (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ univ n ε).log =
          ((Real.log (separatedPartitionSum T φ univ n ε).toReal/n : ℝ) : EReal) := by
        rw [ENNReal.log_pos_real nonzero finite,←EReal.coe_mul]
        congr 1
        ring
      rw [identity]
      exact EReal.coe_le_coe_iff.mpr (by linarith [bound n hn])
    have convergence := continuous_coe_real_ereal.continuousAt.tendsto.comp
      (((P.entropyRate_tendsto T (μ : Measure X) invariant).add_const
        (∫ x, φ x ∂(μ : Measure X))).sub_const (2*η))
    simp only [Function.comp_def] at convergence
    have limit := limsup_le_limsup compare
    rw [convergence.limsup_eq] at limit
    have pressureBound := le_iSup (fun ε : {ε : ℝ // 0 < ε} =>
      limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
        (separatedPartitionSum T φ univ n ε.val).log) atTop) ⟨ε,εpositive⟩
    have result := limit.trans pressureBound
    change _ ≤ pressure T φ univ at result
    rw [pressurePr] at result
    exact EReal.coe_le_coe_iff.mp result
  rw [pressurePr]
  apply EReal.coe_le_coe_iff.mpr
  by_contra failure
  have ηpositive : 0 < (P.entropyRate T (μ : Measure X)+(∫ x, φ x ∂(μ : Measure X))-Pr)/4 := by linarith
  have h := slack _ ηpositive
  linarith

theorem entropy_free_energy_le_pressure (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (φ : X →ᵇ ℝ) :
    entropy T (μ : Measure X) + ((∫ x, φ x ∂(μ : Measure X) : ℝ) : EReal) ≤ pressure T φ univ := by
  obtain ⟨k,P,_,mesh,_,_⟩ := exists_expansive_null_boundary_generator T c positive expansive (μ : Measure X)
  rw [P.entropy_eq_generator_rate T c expansive (fun i x y hx hy => (mesh i x y hx hy).le) μ invariant,
    ←EReal.coe_add]
  exact P.free_energy_le_pressure T c positive expansive μ invariant φ

end LeanShared.ThermodynamicDefinitions
