module
public import LeanShared.Dynamics.CesaroCylinderBoundaryLoss
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Actual weak limits of finite Gibbs Cesaro probabilities inherit the
uniform open-cylinder upper bound. The finite-word boundary loss vanishes;
no Gibbs property of the limiting probability is a hypothesis. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanShared.CesaroProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem cylinder_bound_of_limit (T : X → X) (measurableT : Measurable T)
    (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (ι : ℕ → ℕ) (mono : StrictMono ι)
    (weak : Tendsto (fun j => probabilityMeasure T (μ (ι j)) (ι j)) atTop (𝓝 ν))
    (k : ℕ) (K : ℝ) (nonnegativeK : 0 ≤ K) (U : Set X) (openU : IsOpen U)
    (interior : ∀ n j : ℕ, j < n + 1 → 0 < j → j + k < n + 1 →
      (μ n : Measure X).real ((T^[j]) ⁻¹' U) ≤ K) :
    (ν : Measure X) U ≤ ENNReal.ofReal K := by
  have bounds (n : ℕ) : (probabilityMeasure T (μ n) n : Measure X) U ≤
      ENNReal.ofReal (K + ((k + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) := by
    have bound := cylinder_mass_bound T measurableT (μ n) n k K nonnegativeK
      U openU.measurableSet (interior n)
    change (measure T (μ n) n) U ≤ _
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal bound
  have vanishes : Tendsto (fun j : ℕ => ((k + 1 : ℕ) : ℝ) / (ι j + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, one_div, Function.comp_def, one_mul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp mono.tendsto_atTop).const_mul
        ((k + 1 : ℕ) : ℝ)
  have limit : Tendsto (fun j : ℕ =>
      ENNReal.ofReal (K + ((k + 1 : ℕ) : ℝ) / (ι j + 1 : ℝ)))
      atTop (𝓝 (ENNReal.ofReal K)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using vanishes.const_add K
  have upper := liminf_le_liminf (f := atTop) (Eventually.of_forall (fun j => bounds (ι j)))
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto weak openU).trans
    (upper.trans_eq limit.liminf_eq)

end LeanShared.CesaroProbability
