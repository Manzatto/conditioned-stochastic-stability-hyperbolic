module

public import LeanShared.Dynamics.ExpansivePartitionCoding

/-! A finite measurable observation gives the literal finite measurable
partition used in the entropy definition. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [MeasurableSingletonClass I] [Fintype I]
namespace MeasurablePartition

@[expose] def of_finite_map (f : X → I) (measurable : Measurable f) :
    MeasurablePartition (X := X) (Fintype.card I) where
  atom j := f ⁻¹' {((Fintype.equivFin I).symm j)}
  measurable _ := (measurableSet_singleton _).preimage measurable
  disjoint := by
    intro i j different
    apply Disjoint.preimage _
    exact disjoint_singleton.mpr (fun equal => different ((Fintype.equivFin I).symm.injective equal))
  covering := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨(Fintype.equivFin I) (f x),by simp⟩

theorem of_finite_map_label (f : X → I) (measurable : Measurable f) (x : X) :
    (of_finite_map f measurable).label x=(Fintype.equivFin I) (f x) := by
  apply ((of_finite_map f measurable).label_eq_iff _ _).mpr
  simp [of_finite_map]

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
