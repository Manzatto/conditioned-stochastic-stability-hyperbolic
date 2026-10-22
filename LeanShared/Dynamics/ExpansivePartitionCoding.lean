module

public import LeanShared.Dynamics.SmallBoundaryPartition
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! A small-mesh partition of a compact expansive system is a genuine
measurable generator: its two-sided itinerary is a measurable embedding. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

theorem exists_label (P : MeasurablePartition (X := X) k) (x : X) :
    ∃ i, x ∈ P.atom i := by
  have h : x ∈ ⋃ i, P.atom i := by rw [P.covering]; exact mem_univ x
  exact mem_iUnion.mp h

@[expose] def label (P : MeasurablePartition (X := X) k) (x : X) : Fin k :=
  Classical.choose (exists_label P x)

theorem label_mem (P : MeasurablePartition (X := X) k) (x : X) : x ∈ P.atom (P.label x) :=
  Classical.choose_spec (exists_label P x)

theorem label_eq_iff (P : MeasurablePartition (X := X) k) (x : X) (i : Fin k) :
    P.label x=i ↔ x ∈ P.atom i := by
  constructor
  · intro h; rw [←h]; exact P.label_mem x
  · intro h
    by_contra different
    exact (Set.disjoint_left.mp (P.disjoint different)) (P.label_mem x) h

theorem label_measurable (P : MeasurablePartition (X := X) k) : Measurable P.label := by
  intro s _
  have identity : P.label ⁻¹' s = ⋃ i ∈ s, P.atom i := by
    ext x
    constructor
    · intro h; exact mem_iUnion₂.mpr ⟨P.label x,h,P.label_mem x⟩
    · intro h
      obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp h
      change P.label x ∈ s
      rwa [(P.label_eq_iff x i).mpr hx]
  rw [identity]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => P.measurable i))

variable [MetricSpace X] [BorelSpace X]

/-- The actual pair of future and past itineraries. -/
@[expose] def itinerary (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X) (x : X) :
    (ℕ → Fin k) × (ℕ → Fin k) :=
  ⟨fun n => P.label ((T : X → X)^[n] x), fun n => P.label ((T.symm : X → X)^[n] x)⟩

theorem itinerary_measurable (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X) :
    Measurable (P.itinerary T) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun n => P.label_measurable.comp (T.continuous.measurable.iterate n))
  · exact measurable_pi_iff.mpr (fun n => P.label_measurable.comp (T.symm.continuous.measurable.iterate n))

omit [BorelSpace X] in
/-- Expansivity makes every small-mesh itinerary injective. -/
theorem itinerary_injective (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c) :
    Injective (P.itinerary T) := by
  intro x y equal
  apply expansive x y
  intro n
  have future := congrFun (congrArg Prod.fst equal) n
  have past := congrFun (congrArg Prod.snd equal) n
  exact ⟨mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp future.symm),
    mesh _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp past.symm)⟩

/-- This proves generation of the full Borel sigma algebra, not just
point separation or a prescribed finite coding. -/
theorem itinerary_measurableEmbedding [CompactSpace X]
    (P : MeasurablePartition (X := X) k) (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y ≤ c) :
    MeasurableEmbedding (P.itinerary T) :=
  (P.itinerary_measurable T).measurableEmbedding (P.itinerary_injective T c expansive mesh)

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
