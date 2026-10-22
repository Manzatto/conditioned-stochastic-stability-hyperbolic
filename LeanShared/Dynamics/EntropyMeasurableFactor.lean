module

public import LeanShared.Dynamics.ObservationPartitionEntropy
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! Actual full metric entropy decreases under measurable factors,
using the literal finite measurable partitions and actual pushed measure. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
namespace MeasurablePartition

@[expose] def pullback (P : MeasurablePartition (X := Y) k)
    (f : X → Y) (measurable : Measurable f) : MeasurablePartition (X := X) k where
  atom i := f ⁻¹' P.atom i
  measurable i := (P.measurable i).preimage measurable
  disjoint := fun _ _ different => (P.disjoint different).preimage f
  covering := by rw [←preimage_iUnion,P.covering,preimage_univ]

theorem dynamicalEntropy_pullback (P : MeasurablePartition (X := Y) k)
    (f : X → Y) (measurable : Measurable f) (T : X → X) (S : Y → Y)
    (intertwine : Semiconj f T S) (measurableS : Measurable S) (μ : Measure X) (n : ℕ) :
    dynamicalEntropy (P.pullback f measurable) T μ n =
      dynamicalEntropy P S (μ.map f) n := by
  have atoms (w : Fin n → Fin k) :
      dynamicalAtom (P.pullback f measurable) T n w=f ⁻¹' dynamicalAtom P S n w := by
    ext x
    simp only [dynamicalAtom,mem_iInter,mem_preimage,pullback]
    exact forall_congr' (fun i => by rw [(intertwine.iterate_right i.val) x])
  unfold dynamicalEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  simp only [Measure.real,Measure.map_apply measurable (P.dynamicalAtom_measurable S measurableS n w),←atoms]

end MeasurablePartition

theorem entropy_map_le (f : X → Y) (measurable : Measurable f)
    (T : X → X) (S : Y → Y) (intertwine : Semiconj f T S)
    (measurableS : Measurable S) (μ : Measure X) : entropy S (μ.map f) ≤ entropy T μ := by
  unfold entropy
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  simp_rw [←P.dynamicalEntropy_pullback f measurable T S intertwine measurableS μ]
  exact le_iSup_of_le k (le_iSup_of_le (P.pullback f measurable) le_rfl)

end LeanShared.ThermodynamicDefinitions
