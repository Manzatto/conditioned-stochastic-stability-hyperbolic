module
public import LeanShared.Dynamics.FiniteAtomicProbability

/-! Literal cylinder masses of the constructed finite Gibbs probability are
the corresponding weighted sums divided by its actual partition function. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteAtomicProbability
variable {X I : Type*} [MeasurableSpace X] [Fintype I] [Nonempty I]

theorem gibbs_apply (a : I → ℝ) (x : I → X) (U : Set X) [DecidablePred (fun i => x i ∈ U)]
    (measurable : MeasurableSet U) :
    (gibbs a x : Measure X) U = ENNReal.ofReal
      ((∑ i ∈ Finset.univ.filter (fun i => x i ∈ U), Real.exp (a i)) /
        FiniteGibbsOptimizer.partition a) := by
  classical
  change (measure (FiniteGibbsOptimizer.weights a) x) U = _
  rw [measure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurable, Set.indicator_apply, Pi.one_apply]
  have term (i : I) : ENNReal.ofReal (FiniteGibbsOptimizer.weights a i) *
      (if x i ∈ U then 1 else 0) =
      ENNReal.ofReal (if x i ∈ U then FiniteGibbsOptimizer.weights a i else 0) := by
    split_ifs <;> simp
  simp_rw [term]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    split_ifs
    · exact (FiniteGibbsOptimizer.weights_positive a i).le
    · exact le_rfl)]
  congr 1
  rw [← Finset.sum_filter]
  simp only [FiniteGibbsOptimizer.weights, Finset.sum_div]

end LeanShared.FiniteAtomicProbability
