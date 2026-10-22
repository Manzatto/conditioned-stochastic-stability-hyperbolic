module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecificLimits.Basic

/-! A finite reference can be enlarged to a finite reference whose null
sets are preserved by preimages of a measurable embedding. The explicit
geometric mixture of forward pushforwards also characterizes its null sets. -/

public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ForwardNullReference
variable {X : Type*} [MeasurableSpace X]

@[expose] def reference (f : X → X) (μ : Measure X) : Measure X :=
  Measure.sum (fun n : ℕ => ((2 : ENNReal)⁻¹)^n • μ.map (f^[n]))

theorem iterate_embedding (f : X → X) (embedding : MeasurableEmbedding f) (n : ℕ) :
    MeasurableEmbedding (f^[n]) := by
  induction n with
  | zero => exact MeasurableEmbedding.id
  | succ n ih => simpa only [iterate_succ'] using embedding.comp ih

theorem null_iff (f : X → X) (embedding : MeasurableEmbedding f) (μ : Measure X) (B : Set X) :
    reference f μ B = 0 ↔ ∀ n : ℕ, μ ((f^[n]) ⁻¹' B) = 0 := by
  rw [reference, Measure.sum_apply_eq_zero]
  apply forall_congr'
  intro n
  rw [Measure.smul_apply, (iterate_embedding f embedding n).map_apply]
  have positive : ((2 : ENNReal)⁻¹)^n ≠ 0 := pow_ne_zero n (by norm_num)
  simp only [smul_eq_mul, mul_eq_zero, positive, false_or]

theorem finite (f : X → X) (embedding : MeasurableEmbedding f) (μ : Measure X)
    [IsFiniteMeasure μ] : IsFiniteMeasure (reference f μ) := by
  constructor
  have total : reference f μ univ = 2 * μ univ := by
    simp only [reference, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      Measure.map_apply (embedding.measurable.iterate _) MeasurableSet.univ,
      preimage_univ, smul_eq_mul, ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  rw [total]
  exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top μ univ)

theorem absolutelyContinuous (f : X → X) (embedding : MeasurableEmbedding f) (μ : Measure X) :
    μ ≪ reference f μ := by
  intro B null
  exact (null_iff f embedding μ B).mp null 0

theorem preimage_null (f : X → X) (embedding : MeasurableEmbedding f) (μ : Measure X)
    (B : Set X) (null : reference f μ B = 0) : reference f μ (f ⁻¹' B) = 0 := by
  apply (null_iff f embedding μ (f ⁻¹' B)).mpr
  intro n
  have next := (null_iff f embedding μ B).mp null (n+1)
  simpa only [iterate_succ', preimage_comp] using next

theorem density_transport (f : X → X) (embedding : MeasurableEmbedding f) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (dominated : ν ≪ μ) :
    (reference f μ).withDensity (ν.rnDeriv (reference f μ)) = ν := by
  have := finite f embedding μ
  exact Measure.withDensity_rnDeriv_eq ν (reference f μ)
    (dominated.trans (absolutelyContinuous f embedding μ))

end LeanShared.ForwardNullReference
