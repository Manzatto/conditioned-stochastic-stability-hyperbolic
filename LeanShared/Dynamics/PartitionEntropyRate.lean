module

public import LeanShared.Dynamics.DynamicalEntropySubadditive
public import LeanShared.Dynamics.DynamicalEntropyBounds
public import LeanShared.Dynamics.PartitionEntropyContinuity
public import Mathlib.Topology.Semicontinuity.Basic

/-! Fekete convergence of actual partition entropies and upper
semicontinuity at every invariant probability with null atom boundaries. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

/-- The infimum formula uses all strictly positive observation horizons. -/
@[expose] def entropyRate (P : MeasurablePartition (X := X) k) (T : X → X)
    (μ : Measure X) : ℝ := sInf ((fun n : ℕ => dynamicalEntropy P T μ n / n) '' Ici 1)

private theorem ratios_bddBelow (P : MeasurablePartition (X := X) k) (T : X → X)
    (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ] :
    BddBelow (range (fun n : ℕ => dynamicalEntropy P T μ n / n)) := by
  refine ⟨0,?_⟩
  rintro y ⟨n,rfl⟩
  exact div_nonneg (P.dynamicalEntropy_bounds T measurable μ n).1 (Nat.cast_nonneg n)

/-- The entropy rate is bounded by every positive-time normalized entropy. -/
theorem entropyRate_le_div (P : MeasurablePartition (X := X) k) (T : X → X)
    (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (positive : 0 < n) :
    P.entropyRate T μ ≤ dynamicalEntropy P T μ n / n := by
  apply csInf_le ((P.ratios_bddBelow T measurable μ).mono (image_subset_range _ _))
  exact ⟨n,positive,rfl⟩

/-- Actual normalized finite-time entropies converge, by proved
subadditivity and their nonnegative lower bound. -/
theorem entropyRate_tendsto (P : MeasurablePartition (X := X) k) (T : X → X)
    (μ : Measure X) [IsProbabilityMeasure μ] (invariant : MeasurePreserving T μ μ) :
    Tendsto (fun n : ℕ => dynamicalEntropy P T μ n / n) atTop (𝓝 (P.entropyRate T μ)) := by
  simpa only [entropyRate,Subadditive.lim] using
    (P.dynamicalEntropy_subadditive T μ invariant).tendsto_lim (P.ratios_bddBelow T invariant.measurable μ)

/-- The manuscript's extended-real liminf equals the actual real Fekete
limit; no partition entropy scalar or limit law is a source premise. -/
theorem liminf_eq_entropyRate (P : MeasurablePartition (X := X) k) (T : X → X)
    (μ : Measure X) [IsProbabilityMeasure μ] (invariant : MeasurePreserving T μ μ) :
    liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal)) atTop =
      (P.entropyRate T μ : EReal) := by
  have convergence := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (P.entropyRate_tendsto T μ invariant)
  simpa only [Function.comp_def,div_eq_mul_inv,mul_comm] using convergence.liminf_eq

variable [MetricSpace X] [BorelSpace X]

/-- The infimum entropy rate is upper semicontinuous at a null-boundary
invariant law, even allowing neighboring laws that are not invariant. -/
theorem entropyRate_upperSemicontinuousAt (P : MeasurablePartition (X := X) k)
    (T : X → X) (continuous : Continuous T) (μ : ProbabilityMeasure X)
    (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (boundary : ∀ i, (μ : Measure X) (frontier (P.atom i))=0) :
    UpperSemicontinuousAt (fun ν : ProbabilityMeasure X => P.entropyRate T (ν : Measure X)) μ := by
  intro y above
  obtain ⟨q,⟨n,positive,rfl⟩,below⟩ := exists_lt_of_csInf_lt
    (s := (fun n : ℕ => dynamicalEntropy P T (μ : Measure X) n / n) '' Ici 1)
    (by exact ⟨_,⟨(1 : ℕ),by simp,rfl⟩⟩) above
  have convergence := (P.dynamicalEntropy_tendsto T continuous μ id tendsto_id invariant boundary n).div_const (n : ℝ)
  filter_upwards [convergence.eventually (gt_mem_nhds below)] with ν hν
  exact (P.entropyRate_le_div T continuous.measurable (ν : Measure X) n positive).trans_lt hν

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
