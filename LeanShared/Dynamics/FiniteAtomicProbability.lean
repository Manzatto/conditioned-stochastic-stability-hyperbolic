module

public import LeanShared.Dynamics.FiniteGibbsOptimizer
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual finite atomic probabilities and Gibbs orbit distributions,
constructed from normalized real weights. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ENNReal
namespace LeanShared.FiniteAtomicProbability
variable {X I : Type*} [MeasurableSpace X] [Fintype I]

@[expose] def measure (w : I → ℝ) (x : I → X) : Measure X :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i)

theorem probability (w : I → ℝ) (x : I → X) (nonnegative : ∀ i, 0 ≤ w i)
    (total : ∑ i, w i=1) : IsProbabilityMeasure (measure w x) := by
  constructor
  simp only [measure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),
    smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => nonnegative i),total,ENNReal.ofReal_one]

theorem integral [MeasurableSingletonClass X] (w : I → ℝ) (x : I → X)
    (nonnegative : ∀ i, 0 ≤ w i) (f : X → ℝ) :
    (∫ y, f y ∂measure w x)=∑ i, w i*f (x i) := by
  rw [measure,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (nonnegative _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

@[expose] def probabilityMeasure (w : I → ℝ) (x : I → X) (nonnegative : ∀ i, 0 ≤ w i)
    (total : ∑ i, w i=1) : ProbabilityMeasure X := ⟨measure w x,probability w x nonnegative total⟩

/-- The actual finite Gibbs probability on any specified finite family
of points, without an assumed probability or variational state. -/
@[expose] def gibbs [Nonempty I] (a : I → ℝ) (x : I → X) : ProbabilityMeasure X :=
  probabilityMeasure (FiniteGibbsOptimizer.weights a) x
    (fun i => (FiniteGibbsOptimizer.weights_positive a i).le) (FiniteGibbsOptimizer.weights_total a)

theorem gibbs_integral [Nonempty I] [MeasurableSingletonClass X]
    (a : I → ℝ) (x : I → X) (f : X → ℝ) :
    (∫ y, f y ∂(gibbs a x : Measure X))=∑ i, FiniteGibbsOptimizer.weights a i*f (x i) :=
  integral _ _ (fun i => (FiniteGibbsOptimizer.weights_positive a i).le) f

end LeanShared.FiniteAtomicProbability
