module

public import LeanShared.Dynamics.FiniteObservationEntropy

/-! Strong subadditivity for actual finite measurable observations. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I J K : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

theorem strong_subadditivity (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → I) (f : X → J) (h : X → K)
    (measurableG : Measurable g) (measurableF : Measurable f) (measurableH : Measurable h) :
    entropy μ (fun x => (g x,(f x,h x))) + entropy μ g ≤
      entropy μ (fun x => (g x,f x)) + entropy μ (fun x => (g x,h x)) := by
  let A := fun i => g ⁻¹' {i}
  let B := fun j => f ⁻¹' {j}
  let C := fun k => h ⁻¹' {k}
  have measurableA (i : I) : MeasurableSet (A i) := (measurableSet_singleton i).preimage measurableG
  have measurableB (j : J) : MeasurableSet (B j) := (measurableSet_singleton j).preimage measurableF
  have row (i : I) (j : J) : ∑ k, μ.real ((A i ∩ B j) ∩ C k)=μ.real (A i ∩ B j) :=
    marginal μ _ ((measurableA i).inter (measurableB j)) h measurableH
  have col (i : I) (k : K) : ∑ j, μ.real ((A i ∩ B j) ∩ C k)=μ.real (A i ∩ C k) := by
    have identity (j : J) : (A i ∩ B j) ∩ C k=(A i ∩ C k) ∩ B j := by
      ext x
      simp only [mem_inter_iff,and_right_comm]
    simp_rw [identity]
    exact marginal μ _ ((measurableA i).inter ((measurableSet_singleton k).preimage measurableH)) f measurableF
  have base (i : I) : ∑ j, ∑ k, μ.real ((A i ∩ B j) ∩ C k)=μ.real (A i) := by
    simp_rw [row]
    exact marginal μ _ (measurableA i) f measurableF
  have cube : entropy μ (fun x => (g x,(f x,h x))) =
      -(∑ i, ∑ j, ∑ k, μ.real ((A i ∩ B j) ∩ C k)*Real.log (μ.real ((A i ∩ B j) ∩ C k))) := by
    rw [pair_entropy]
    simp_rw [Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have fiber : g ⁻¹' {i} ∩ (fun x => (f x,h x)) ⁻¹' {(j,k)}=(A i ∩ B j) ∩ C k := by
      ext x
      simp [A,B,C,and_assoc]
    rw [fiber]
  have bound := FiniteStrongSubadditivity.entropy_strong_subadditive
    (fun i j k => μ.real ((A i ∩ B j) ∩ C k)) (fun _ _ _ => measureReal_nonneg)
  simp_rw [col] at bound
  simp_rw [row] at bound
  have base' (i : I) : ∑ j, μ.real (A i ∩ B j)=μ.real (A i) :=
    marginal μ _ (measurableA i) f measurableF
  simp_rw [base'] at bound
  rw [cube,pair_entropy,pair_entropy]
  simpa only [A,B,C,entropy,sub_eq_add_neg] using bound

end LeanShared.FiniteObservationEntropy
