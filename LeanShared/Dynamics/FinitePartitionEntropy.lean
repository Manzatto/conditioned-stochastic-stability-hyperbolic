module

public import LeanShared.Dynamics.FiniteEntropySubadditivity
public import Mathlib.MeasureTheory.Measure.Real

/-! Entropy subadditivity for actual intersections of finite measurable
partitions, with all marginals obtained from finite additivity. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FinitePartitionEntropy
variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]

private theorem marginal (μ : Measure X) [IsFiniteMeasure μ] (A : Set X)
    (B : J → Set X) (measurableA : MeasurableSet A) (measurableB : ∀ j, MeasurableSet (B j))
    (disjointB : Pairwise (fun i j => Disjoint (B i) (B j))) (coverB : ⋃ j, B j=univ) :
    ∑ j, μ.real (A ∩ B j)=μ.real A := by
  rw [←measureReal_iUnion_fintype]
  · rw [←inter_iUnion,coverB,inter_univ]
  · intro i j different
    exact (disjointB different).mono inter_subset_right inter_subset_right
  · exact fun j => measurableA.inter (measurableB j)

/-- The entropy of the common refinement is bounded by the sum of the
actual two partition entropies. -/
theorem refinement_le (μ : Measure X) [IsProbabilityMeasure μ]
    (A : I → Set X) (B : J → Set X)
    (measurableA : ∀ i, MeasurableSet (A i)) (measurableB : ∀ j, MeasurableSet (B j))
    (disjointA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (disjointB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (coverA : ⋃ i, A i=univ) (coverB : ⋃ j, B j=univ) :
    -(∑ i, ∑ j, μ.real (A i ∩ B j)*Real.log (μ.real (A i ∩ B j))) ≤
      -(∑ i, μ.real (A i)*Real.log (μ.real (A i))) -
       (∑ j, μ.real (B j)*Real.log (μ.real (B j))) := by
  have row := fun i => marginal μ (A i) B (measurableA i) measurableB disjointB coverB
  have col (j : J) : ∑ i, μ.real (A i ∩ B j)=μ.real (B j) := by
    simp_rw [inter_comm (A _) (B j)]
    exact marginal μ (B j) A (measurableB j) measurableA disjointA coverA
  have total : ∑ i, ∑ j, μ.real (A i ∩ B j)=1 := by
    simp_rw [row]
    rw [←measureReal_iUnion_fintype disjointA measurableA,coverA]
    simp
  have bound := FiniteEntropySubadditivity.entropy_joint_le
    (fun i j => μ.real (A i ∩ B j)) (fun _ _ => measureReal_nonneg) total
  simpa only [row,col] using bound

end LeanShared.FinitePartitionEntropy
