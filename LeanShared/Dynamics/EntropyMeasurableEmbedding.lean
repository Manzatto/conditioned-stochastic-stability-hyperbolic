module

public import LeanShared.Dynamics.EntropyMeasurableFactor

/-! Full metric entropy is exactly preserved by measurable embeddings
intertwining the actual dynamics, with the actual pushed measure. -/
public noncomputable section
open Set Function Filter MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X]

omit [Nonempty X] in
private theorem partition_ext {k : ℕ} (P Q : MeasurablePartition (X := X) k)
    (same : ∀ i, P.atom i=Q.atom i) : P=Q := by
  cases P
  cases Q
  congr 1
  exact funext same

private theorem exists_partition_extension {k : ℕ} (P : MeasurablePartition (X := X) k)
    (f : X → Y) (embedding : MeasurableEmbedding f) :
    ∃ Q : MeasurablePartition (X := Y) k, Q.pullback f embedding.measurable=P := by
  classical
  obtain ⟨g,measurable,equal⟩ := embedding.exists_measurable_extend P.label_measurable
    (fun _ => ⟨P.label (Classical.arbitrary X)⟩)
  let Q : MeasurablePartition (X := Y) k :=
    ⟨(fun i => g ⁻¹' {i}),(fun i => (measurableSet_singleton i).preimage measurable),
      (fun _ _ different => (disjoint_singleton.mpr different).preimage g),by
        apply eq_univ_of_forall
        intro y
        exact mem_iUnion.mpr ⟨g y,rfl⟩⟩
  refine ⟨Q,partition_ext _ _ ?_⟩
  intro i
  ext x
  change g (f x)=i ↔ x ∈ P.atom i
  have pointwise := congrFun equal x
  change g (f x)=P.label x at pointwise
  rw [pointwise]
  exact P.label_eq_iff x i

theorem entropy_map_embedding (f : X → Y) (embedding : MeasurableEmbedding f)
    (T : X → X) (S : Y → Y) (intertwine : Semiconj f T S)
    (measurableS : Measurable S) (μ : Measure X) : entropy S (μ.map f)=entropy T μ := by
  apply le_antisymm (entropy_map_le f embedding.measurable T S intertwine measurableS μ)
  unfold entropy
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  obtain ⟨Q,equal⟩ := exists_partition_extension P f embedding
  have same (n : ℕ) := Q.dynamicalEntropy_pullback f embedding.measurable T S intertwine measurableS μ n
  rw [equal] at same
  simp_rw [same]
  exact le_iSup_of_le k (le_iSup_of_le Q le_rfl)

end LeanShared.ThermodynamicDefinitions
