module

public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.PartitionObservationConditional

/-! Exact one-observation Shannon identities for the actual finite
partition atoms, retaining zero atoms. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions.MeasurablePartition
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

theorem atom_masses_total (P : MeasurablePartition (X := X) k) (μ : Measure X)
    [IsProbabilityMeasure μ] : ∑ i, μ.real (P.atom i) = 1 := by
  rw [← measureReal_iUnion_fintype P.disjoint P.measurable, P.covering]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one]

theorem entropy_label_atoms (P : MeasurablePartition (X := X) k) (μ : Measure X) :
    LeanShared.FiniteObservationEntropy.entropy μ P.label =
      -(∑ i, μ.real (P.atom i) * Real.log (μ.real (P.atom i))) := by
  simp only [LeanShared.FiniteObservationEntropy.entropy, P.label_fiber]

theorem dynamicalEntropy_one (P : MeasurablePartition (X := X) k) (T : X → X) (μ : Measure X) :
    dynamicalEntropy P T μ 1 = -(∑ i, μ.real (P.atom i) * Real.log (μ.real (P.atom i))) := by
  let constant : Fin k → (Fin 1 → Fin k) := fun i _ => i
  have injective : Injective constant := by
    intro i j equal
    exact congrFun equal ⟨0, by omega⟩
  have same : P.wordObservation T 1 = constant ∘ P.label := by
    funext x i
    have zero : i.val = 0 := by omega
    simp only [wordObservation, zero, iterate_zero, id_eq, comp_apply, constant]
  rw [← P.wordObservation_entropy T μ 1, same,
    LeanShared.FiniteObservationEntropy.entropy_injective μ P.label constant injective]
  exact P.entropy_label_atoms μ

end LeanShared.ThermodynamicDefinitions.MeasurablePartition
