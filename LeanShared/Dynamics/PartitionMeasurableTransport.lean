module

public import LeanShared.Dynamics.ExpansivePartitionCoding

/-! Measurable bijections transport actual finite partitions and their
literal labels. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

@[expose] def comap (P : MeasurablePartition (X := X) k) (S : X → X) (measurable : Measurable S) :
    MeasurablePartition (X := X) k where
  atom i := S ⁻¹' P.atom i
  measurable i := (P.measurable i).preimage measurable
  disjoint := fun i j different => (P.disjoint different).preimage S
  covering := by rw [←preimage_iUnion,P.covering,preimage_univ]

theorem comap_label (P : MeasurablePartition (X := X) k) (S : X → X)
    (measurable : Measurable S) (x : X) : (P.comap S measurable).label x=P.label (S x) := by
  apply ((P.comap S measurable).label_eq_iff x (P.label (S x))).mpr
  exact P.label_mem (S x)

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
