module

public import LeanShared.Dynamics.ExpansivePartitionCoding
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Real

/-! Prediction in probability gives vanishing actual conditional entropy
for a fixed finite target partition, including all null atoms. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

/-- The joint law of the true atom and a finite predicted label. -/
@[expose] def predictionJoint (P : MeasurablePartition (X := X) k)
    (μ : Measure X) (f : X → Fin k) (i j : Fin k) : ℝ := μ.real (P.atom i ∩ f ⁻¹' {j})

/-- Vanishing classification error implies vanishing conditional Shannon
entropy of the actual true and predicted labels. -/
theorem prediction_conditionalEntropy_tendsto (P : MeasurablePartition (X := X) k)
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → Fin k) (measurable : ∀ n, Measurable (f n))
    (error : Tendsto (fun n => μ.real {x | P.label x ≠ f n x}) atTop (𝓝 0)) :
    Tendsto (fun n =>
      -(∑ i, ∑ j, P.predictionJoint μ (f n) i j*Real.log (P.predictionJoint μ (f n) i j)) +
      ∑ j, (∑ i, P.predictionJoint μ (f n) i j)*Real.log (∑ i, P.predictionJoint μ (f n) i j))
      atTop (𝓝 0) := by
  classical
  have entry_bound (n : ℕ) (i j : Fin k) :
      ‖P.predictionJoint μ (f n) i j - (if i=j then μ.real (P.atom i) else 0)‖ ≤
        μ.real {x | P.label x ≠ f n x} := by
    by_cases equal : i=j
    · subst j
      rw [ite_eq_left rfl]
      have missing : P.atom i \ f n ⁻¹' {i} ⊆ {x | P.label x ≠ f n x} := by
        intro x hx same
        apply hx.2
        change f n x=i
        exact same.symm.trans ((P.label_eq_iff x i).mpr hx.1)
      have equation := measureReal_sdiff_add_inter (μ := μ) (s := P.atom i)
        ((measurableSet_singleton i).preimage (measurable n))
      have lower : P.predictionJoint μ (f n) i i ≤ μ.real (P.atom i) := measureReal_mono inter_subset_left
      have identity : ‖P.predictionJoint μ (f n) i i - μ.real (P.atom i)‖ =
          μ.real (P.atom i \ f n ⁻¹' {i}) := by
        rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr lower)]
        dsimp only [predictionJoint] at *
        linarith
      rw [identity]
      exact measureReal_mono missing
    · rw [ite_eq_right equal,sub_zero,Real.norm_eq_abs]
      rw [abs_of_nonneg (show 0 ≤ P.predictionJoint μ (f n) i j from measureReal_nonneg)]
      apply measureReal_mono (h₂ := measure_ne_top μ _)
      intro x hx same
      apply equal
      exact ((P.label_eq_iff x i).mpr hx.1).symm.trans (same.trans hx.2)
  have entries (i j : Fin k) : Tendsto (fun n => P.predictionJoint μ (f n) i j) atTop
      (𝓝 (if i=j then μ.real (P.atom i) else 0)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => entry_bound n i j) error
  have joint := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      Real.continuous_mul_log.continuousAt.tendsto.comp (entries i j)))
  have columns (j : Fin k) := tendsto_finsetSum Finset.univ (fun i _ => entries i j)
  have marginal := tendsto_finsetSum Finset.univ (fun j _ =>
    Real.continuous_mul_log.continuousAt.tendsto.comp (columns j))
  have result := joint.neg.add marginal
  simpa only [Function.comp_apply,apply_ite (fun x : ℝ => x*Real.log x),Real.log_zero,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_ite_eq,neg_add_cancel] using result

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
