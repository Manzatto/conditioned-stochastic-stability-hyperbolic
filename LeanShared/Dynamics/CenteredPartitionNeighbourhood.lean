module

public import LeanShared.Dynamics.ExpansiveCenteredCylinderContainment
public import LeanShared.Dynamics.ExpansivePartitionCoding

/-! Centering a sufficiently long Bowen-small partition produces a finite
union of its cells between any compact set and any open neighbourhood.
The detector length is chosen before the partition. -/
public noncomputable section
open Set Function
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]

theorem exists_centered_partition_union (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (K U : Set X) (compact : IsCompact K) (opened : IsOpen U) (inside : K ⊆ U) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ Q : MeasurablePartition (X := X) k,
      (∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i →
        ∀ j ≤ 2 * N, dist (T^[j] x) (T^[j] y) ≤ c) →
      ∃ s : Finset (Fin k),
        K ⊆ ⋃ i ∈ s, ((T.symm : X → X)^[N]) ⁻¹' Q.atom i ∧
        (⋃ i ∈ s, ((T.symm : X → X)^[N]) ⁻¹' Q.atom i) ⊆ U := by
  classical
  obtain ⟨N, detect⟩ := FiniteExpansiveWords.exists_centered_cylinder_containment
    T c expansive K U compact opened inside
  refine ⟨N, fun k Q mesh => ?_⟩
  let R := fun i => ((T.symm : X → X)^[N]) ⁻¹' Q.atom i
  let s := Finset.univ.filter (fun i => (R i ∩ K).Nonempty)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    let i := Q.label ((T.symm : X → X)^[N] x)
    have member : x ∈ R i := Q.label_mem _
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, member, hx⟩, member⟩
  · intro x hx
    obtain ⟨i, hi, member⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyR, hyK⟩ := (Finset.mem_filter.mp hi).2
    have close := mesh i ((T.symm : X → X)^[N] x) ((T.symm : X → X)^[N] y) member hyR
    have belongs := detect y hyK ((T.symm : X → X)^[N] x)
      (fun j hj => close j (by omega))
    have cancel : (T : X → X)^[N] ((T.symm : X → X)^[N] x) = x := T.right_inv.iterate N x
    rwa [cancel] at belongs

end LeanShared.ThermodynamicDefinitions
