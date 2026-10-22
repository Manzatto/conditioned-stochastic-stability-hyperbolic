module

public import LeanShared.Dynamics.SeparatedSpanningSet
public import LeanShared.Dynamics.ExpansivePartitionCoding
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Actual maximal separated sets give measurable Bowen-cover partitions
with one separated center for each atom. -/
public noncomputable section
open Set Function
namespace LeanShared.ThermodynamicDefinitions
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]

theorem exists_bowen_cover_partition (T : X → X) (continuous : Continuous T)
    (n : ℕ) (ε : ℝ) (positive : 0 < ε) (C : ℕ)
    (count : ∀ s : Finset X, Separated T univ n ε s → s.card ≤ C) :
    ∃ (k : ℕ) (P : MeasurablePartition (X := X) k) (center : Fin k → X),
      0 < k ∧ Injective center ∧
      Separated T univ n ε (Finset.univ.image center) ∧
      ∀ i x, x ∈ P.atom i → ∀ j < n, dist (T^[j] x) (T^[j] (center i)) < ε := by
  classical
  obtain ⟨s,nonempty,separated,spanning⟩ := exists_separated_spanning T n ε positive C count
  let : Nonempty s := nonempty.to_subtype
  let k := Fintype.card s
  let e : Fin k ≃ s := (Fintype.equivFin s).symm
  let center : Fin k → X := fun i => (e i).val
  let V (i : Fin k) : Set X := {x | ∀ j < n, dist (T^[j] x) (T^[j] (center i)) < ε}
  have measurable (i : Fin k) : MeasurableSet (V i) := by
    have eq : V i = ⋂ j : ℕ, ⋂ (_ : j < n), {x | dist (T^[j] x) (T^[j] (center i)) < ε} := by
      ext x
      simp only [V,mem_iInter,mem_ofPred_eq]
    rw [eq]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      (isOpen_lt ((continuous.iterate j).dist continuous_const) continuous_const).measurableSet))
  have cover : ⋃ i, V i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y,hy,near⟩ := spanning x
    exact mem_iUnion.mpr ⟨e.symm ⟨y,hy⟩,by simpa only [V,center,Equiv.apply_symm_apply,mem_ofPred_eq] using near⟩
  let P : MeasurablePartition (X := X) k :=
    ⟨disjointed V,(fun i => by
      rw [disjointed_eq_inter_compl]
      exact (measurable i).inter (MeasurableSet.iInter (fun j =>
        MeasurableSet.iInter (fun _ => (measurable j).compl)))),
      disjoint_disjointed V,iUnion_disjointed.trans cover⟩
  have centers : Finset.univ.image center = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (e i).property
    · intro hx
      exact Finset.mem_image.mpr ⟨e.symm ⟨x,hx⟩,Finset.mem_univ _,by simp [center]⟩
  refine ⟨k,P,center,Fintype.card_pos,?_,by rwa [centers],?_⟩
  · exact Subtype.val_injective.comp e.injective
  · intro i x hx
    exact disjointed_subset V i hx

end LeanShared.ThermodynamicDefinitions
