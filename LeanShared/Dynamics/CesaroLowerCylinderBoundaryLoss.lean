module
public import LeanShared.Dynamics.WeakGibbsCylinderUpper
public import Mathlib.Order.Interval.Finset.Nat

/-! Actual finite Gibbs lower bounds away from two transition seams pass
to Cesaro probabilities and their weak limits. Only `(k+2 gap)/N` of the
orbit average is lost; closed-set Portmanteau preserves the SAME limit. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace LeanShared.CesaroProbability

theorem sum_lower_bound (a : ℕ → ℝ) (N k gap : ℕ) (L : ℝ) (nonnegativeL : 0 ≤ L)
    (nonnegative : ∀ j < N, 0 ≤ a j)
    (interior : ∀ j < N, gap ≤ j → j + k + gap < N → L ≤ a j) :
    (N : ℝ) * L - ((k + 2 * gap : ℕ) : ℝ) * L ≤ ∑ j ∈ Finset.range N, a j := by
  let good := Finset.Ico gap (N - k - gap)
  have subset : good ⊆ Finset.range N := by
    intro j hj
    obtain ⟨_, upper⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_range.mpr (by omega)
  have goodLower : (good.card : ℝ) * L ≤ ∑ j ∈ good, a j := by
    have bound := Finset.sum_le_sum (s := good) (fun j hj =>
      interior j (Finset.mem_range.mp (subset hj)) (Finset.mem_Ico.mp hj).1 (by
        have upper := (Finset.mem_Ico.mp hj).2
        omega))
    simpa only [Finset.sum_const, nsmul_eq_mul] using bound
  have sumLower := goodLower.trans (Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun j hj _ => nonnegative j (Finset.mem_range.mp hj)))
  have cardinal : N ≤ good.card + (k + 2 * gap) := by
    simp only [good, Nat.card_Ico]
    omega
  have castCard : (N : ℝ) ≤ (good.card : ℝ) + ((k + 2 * gap : ℕ) : ℝ) := by exact_mod_cast cardinal
  have scaled := mul_le_mul_of_nonneg_right castCard nonnegativeL
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem cylinder_mass_lower_bound (T : X → X) (measurableT : Measurable T)
    (μ : ProbabilityMeasure X) (n k gap : ℕ) (L : ℝ) (nonnegativeL : 0 ≤ L)
    (U : Set X) (measurableU : MeasurableSet U)
    (interior : ∀ j < n + 1, gap ≤ j → j + k + gap < n + 1 →
      L ≤ (μ : Measure X).real ((T^[j]) ⁻¹' U)) :
    L - (((k + 2 * gap : ℕ) : ℝ) * L) / (n + 1 : ℝ) ≤ (measure T μ n).real U := by
  have formula : (measure T μ n).real U = (n + 1 : ℝ)⁻¹ *
      ∑ j ∈ Finset.range (n + 1), (μ : Measure X).real ((T^[j]) ⁻¹' U) := by
    rw [measure, measureReal_ennreal_smul_apply]
    simp only [Measure.real, Measure.finsetSum_apply, ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one]
    rw [ENNReal.toReal_sum (fun _ _ => by finiteness)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_apply (measurableT.iterate j) measurableU]
  rw [formula]
  have bound := sum_lower_bound (fun j => (μ : Measure X).real ((T^[j]) ⁻¹' U))
    (n + 1) k gap L nonnegativeL (fun _ _ => measureReal_nonneg) interior
  have weighted := mul_le_mul_of_nonneg_left bound (show 0 ≤ (n + 1 : ℝ)⁻¹ by positivity)
  convert weighted using 1
  push_cast
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul,
    div_eq_inv_mul]

theorem cylinder_lower_bound_of_limit (T : X → X) (measurableT : Measurable T)
    (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (ι : ℕ → ℕ) (mono : StrictMono ι)
    (weak : Tendsto (fun j => probabilityMeasure T (μ (ι j)) (ι j)) atTop (𝓝 ν))
    (k gap : ℕ) (L : ℝ) (nonnegativeL : 0 ≤ L) (U : Set X) (closedU : IsClosed U)
    (interior : ∀ n j : ℕ, j < n + 1 → gap ≤ j → j + k + gap < n + 1 →
      L ≤ (μ n : Measure X).real ((T^[j]) ⁻¹' U)) :
    ENNReal.ofReal L ≤ (ν : Measure X) U := by
  have bounds (n : ℕ) : ENNReal.ofReal
      (L - (((k + 2 * gap : ℕ) : ℝ) * L) / (n + 1 : ℝ)) ≤
      (probabilityMeasure T (μ n) n : Measure X) U := by
    have bound := cylinder_mass_lower_bound T measurableT (μ n) n k gap L nonnegativeL
      U closedU.measurableSet (interior n)
    change _ ≤ (measure T (μ n) n) U
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal bound
  have vanishes : Tendsto (fun j : ℕ => (((k + 2 * gap : ℕ) : ℝ) * L) / (ι j + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, one_div, Function.comp_def, one_mul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp mono.tendsto_atTop).const_mul
        (((k + 2 * gap : ℕ) : ℝ) * L)
  have limit : Tendsto (fun j : ℕ =>
      ENNReal.ofReal (L - (((k + 2 * gap : ℕ) : ℝ) * L) / (ι j + 1 : ℝ)))
      atTop (𝓝 (ENNReal.ofReal L)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [sub_zero] using vanishes.const_sub L
  have lower := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun j => bounds (ι j)))
  rw [limit.limsup_eq] at lower
  exact lower.trans (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto weak closedU)

end LeanShared.CesaroProbability
