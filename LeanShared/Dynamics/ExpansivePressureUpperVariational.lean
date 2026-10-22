module

public import LeanShared.Dynamics.ExpansiveUniformGibbsBound
public import LeanShared.Dynamics.ExpansiveFinitePressure

/-! The actual separated-set pressure is bounded above by the maximum
of actual Kolmogorov--Sinai entropy plus potential energy. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem pressure_le_variational_maximum
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (φ : X →ᵇ ℝ) (M : ℝ)
    (maximal : ∀ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) →
      (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) ≤ M) :
    pressure T φ univ ≤ (M : EReal) := by
  classical
  have slack (η : ℝ) (ηpositive : 0 < η) : pressure T φ univ ≤ (M+η : ℝ) := by
    unfold pressure
    apply iSup_le
    intro ε
    have uniform := eventual_uniform_separated_free_energy T c positive expansive φ M maximal
      ε.val η ε.property ηpositive
    have bound : ∀ᶠ n : ℕ in atTop,
        ((((n+1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal)*
          (separatedPartitionSum T φ univ (n+1) ε.val).log ≤ (M+η : ℝ) := by
      filter_upwards [uniform] with n hn
      have npos : (0 : ℝ) < n+1 := by positivity
      have partitionBound : separatedPartitionSum T φ univ (n+1) ε.val ≤
          ENNReal.ofReal (Real.exp ((n+1 : ℝ)*(M+η))) := by
        unfold separatedPartitionSum
        refine iSup_le fun s => iSup_le fun hs => ?_
        by_cases nonempty : s.Nonempty
        · have realBound := (div_le_iff₀ npos).mp (hn s nonempty hs)
          have sumpos : 0 < ∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x) :=
            Finset.sum_pos (fun x _ => Real.exp_pos _) nonempty
          rw [←ENNReal.ofReal_sum_of_nonneg (fun x _ => (Real.exp_pos _).le)]
          apply ENNReal.ofReal_le_ofReal
          exact (Real.log_le_iff_le_exp sumpos).mp (by nlinarith [realBound])
        · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty,Finset.sum_empty]
          exact bot_le
      have logs := ENNReal.log_le_log partitionBound
      rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp] at logs
      have scaled := mul_le_mul_of_nonneg_left logs
        (EReal.coe_nonneg.mpr (inv_nonneg.mpr npos.le))
      have identity : ((((n+1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal)*
          (((n+1 : ℝ)*(M+η) : ℝ) : EReal) = (M+η : ℝ) := by
        rw [←EReal.coe_mul]
        congr 1
        push_cast
        field_simp
      simpa only [Nat.cast_add,Nat.cast_one] using
        scaled.trans_eq (by simpa only [Nat.cast_add,Nat.cast_one] using identity)
    have h := limsup_le_limsup bound
    rw [limsup_const] at h
    have shift := limsup_nat_add (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
      (separatedPartitionSum T φ univ n ε.val).log) 1
    rw [←shift]
    exact h
  obtain ⟨P,pressureP⟩ := finite_pressure_of_expansive T c positive expansive φ φ.continuous
  rw [pressureP]
  apply EReal.coe_le_coe_iff.mpr
  by_contra failure
  have high : M < P := lt_of_not_ge failure
  have h := slack ((P-M)/2) (by linarith)
  rw [pressureP] at h
  have real := EReal.coe_le_coe_iff.mp h
  linarith

end LeanShared.ThermodynamicDefinitions
