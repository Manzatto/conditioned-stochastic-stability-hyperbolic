module

public import LeanShared.Dynamics.PartitionObservationConditional
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A uniform classification-error modulus controls actual finite
conditional entropy, without a Fano or entropy-continuity source assumption. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

theorem MeasurablePartition.exists_conditional_error_bound
    (P : MeasurablePartition (X := X) k) (μ : Measure X) [IsFiniteMeasure μ]
    (ε : ℝ) (positive : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : X → Fin k, Measurable f →
      μ.real {x | P.label x ≠ f x} < δ →
      LeanShared.FiniteObservationEntropy.conditional μ P.label f < ε := by
  classical
  by_contra failure
  have bad (n : ℕ) : ∃ f : X → Fin k, Measurable f ∧
      μ.real {x | P.label x ≠ f x} < 1/(n+1 : ℝ) ∧
      ε ≤ LeanShared.FiniteObservationEntropy.conditional μ P.label f := by
    have h := not_exists.mp failure (1/(n+1 : ℝ))
    have h' := not_and.mp h
    have denied := h' (by positivity)
    push Not at denied
    exact denied
  choose f measurable error high using bad
  have vanish : Tendsto (fun n => μ.real {x | P.label x ≠ f n x}) atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg) (fun n => (error n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have conditional := P.prediction_conditional_tendsto μ f measurable vanish
  have low := conditional.eventually (gt_mem_nhds positive)
  obtain ⟨n,hn⟩ := low.exists
  exact (not_lt_of_ge (high n)) hn

end LeanShared.ThermodynamicDefinitions
