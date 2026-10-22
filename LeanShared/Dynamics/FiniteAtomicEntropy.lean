module

public import LeanShared.Dynamics.FiniteAtomicProbability
public import LeanShared.Dynamics.FiniteObservationEntropy

/-! Entropy of a finite atomic probability is the actual weight entropy
whenever the finite observation distinguishes the supported atoms. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanShared.FiniteAtomicProbability
variable {X I J : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [Fintype I] [Fintype J]

theorem real_apply (w : I → ℝ) (x : I → X) (nonnegative : ∀ i, 0 ≤ w i) (A : Set X) :
    (measure w x).real A=∑ i, if x i ∈ A then w i else 0 := by
  classical
  simp only [measure,Measure.real,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_ofReal (nonnegative _),Measure.dirac_apply,Set.indicator_apply,Pi.one_apply,apply_ite ENNReal.toReal,
    ENNReal.toReal_zero,mul_ite,mul_one,mul_zero]

theorem observation_entropy_of_injective (w : I → ℝ) (x : I → X)
    (nonnegative : ∀ i, 0 ≤ w i) (f : X → J) (injective : Injective (f ∘ x)) :
    FiniteObservationEntropy.entropy (measure w x) f = -(∑ i, w i*Real.log (w i)) := by
  classical
  let embedding : I ↪ J := ⟨f ∘ x,injective⟩
  let image := Finset.univ.map embedding
  have fiber (i : I) : (measure w x).real (f ⁻¹' {f (x i)})=w i := by
    rw [real_apply w x nonnegative]
    simp only [mem_preimage,mem_singleton_iff]
    have identity (j : I) : (f (x j)=f (x i)) ↔ j=i := injective.eq_iff
    simp_rw [identity]
    simp
  have outside (j : J) (_ : j ∈ Finset.univ) (notmem : j ∉ image) :
      (measure w x).real (f ⁻¹' {j})*Real.log ((measure w x).real (f ⁻¹' {j}))=0 := by
    have noatom (i : I) : f (x i) ≠ j := by
      intro equal
      exact notmem (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,equal⟩)
    rw [real_apply w x nonnegative]
    simp only [mem_preimage,mem_singleton_iff,noatom,ite_false,Finset.sum_const_zero,zero_mul]
  unfold FiniteObservationEntropy.entropy
  rw [←Finset.sum_subset (Finset.subset_univ image) outside,Finset.sum_map]
  simp only [embedding,Function.Embedding.coeFn_mk,Function.comp_apply,fiber]

end LeanShared.FiniteAtomicProbability
