module

public import LeanShared.Dynamics.DynamicalPartition
public import LeanShared.Dynamics.FinitePartitionEntropy
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Data.Fin.Tuple.Basic
import all LeanShared.Dynamics.DynamicalEntropySubadditive

/-! The literal finite-time entropy inequality for arbitrary initial
probabilities, with the second block evaluated at the actual pushforward. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- No invariance is required: the initial measure of the second block
is the actual n-step pushed-forward probability. -/
theorem MeasurablePartition.dynamicalEntropy_add_le (P : MeasurablePartition (X := X) k)
    (T : X → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (measurable : Measurable T) (n m : ℕ) :
    dynamicalEntropy P T μ (n+m) ≤ dynamicalEntropy P T μ n +
      dynamicalEntropy P T (μ.map (T^[n])) m := by
  let A := dynamicalAtom P T n
  let B := fun w => (T^[n]) ⁻¹' dynamicalAtom P T m w
  have measurableA := P.dynamicalAtom_measurable T measurable n
  have measurableB := fun w => (P.dynamicalAtom_measurable T measurable m w).preimage
    (measurable.iterate n)
  have disjointB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j different
    exact (P.dynamicalAtoms_disjoint T m different).preimage _
  have coverB : ⋃ w, B w=univ := by
    rw [←preimage_iUnion,P.dynamicalAtoms_cover T m,preimage_univ]
  have bound := FinitePartitionEntropy.refinement_le μ A B measurableA measurableB
    (P.dynamicalAtoms_disjoint T n) disjointB (P.dynamicalAtoms_cover T n) coverB
  have joint : dynamicalEntropy P T μ (n+m) =
      -(∑ i, ∑ j, μ.real (A i ∩ B j)*Real.log (μ.real (A i ∩ B j))) := by
    unfold dynamicalEntropy
    rw [←(appendEquiv (k := k) n m).sum_comp]
    simp only [atom_append,Fintype.sum_prod_type,A,B]
  rw [joint]
  have masses (w : Fin m → Fin k) : μ.real (B w)=(μ.map (T^[n])).real (dynamicalAtom P T m w) := by
    simp only [Measure.real,Measure.map_apply (measurable.iterate n)
      (P.dynamicalAtom_measurable T measurable m w),B]
  simpa only [masses,A,dynamicalEntropy,sub_eq_add_neg] using bound

end LeanShared.ThermodynamicDefinitions
