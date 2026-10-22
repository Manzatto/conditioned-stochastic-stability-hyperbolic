module

public import LeanShared.Dynamics.PartitionEntropyContinuity
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Small finite partitions with null boundaries, constructed from balls
and finite disjointization, without a generating-partition assumption. -/
public noncomputable section
open Set Function MeasureTheory Metric
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
private theorem disjointed_frontier_null {k : ℕ} (A : Fin k → Set X)
    (μ : Measure X) (boundary : ∀ i, μ (frontier (A i))=0) (i : Fin k) :
    μ (frontier (disjointed A i))=0 := by
  apply disjointedRec (p := fun s : Set X => μ (frontier s)=0) (fun {t j} ht => ?_) (boundary i)
  have h : frontier (t \ A j) ⊆ frontier t ∪ frontier (A j) := by
    have h := frontier_inter_subset t (A j)ᶜ
    rw [frontier_compl] at h
    exact h.trans (union_subset_union inter_subset_left inter_subset_right)
  exact measure_mono_null h (measure_union_null ht (boundary j))

/-- Every finite Borel measure on a compact metric space admits finite
measurable partitions of arbitrarily small mesh with null boundaries. -/
theorem exists_small_boundary_partition [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (ε : ℝ) (positive : 0 < ε) :
    ∃ k : ℕ, ∃ P : MeasurablePartition (X := X) k,
      (∀ i, μ (frontier (P.atom i))=0) ∧
      ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y < ε := by
  classical
  have radii (x : X) : ∃ r ∈ Ioo 0 (ε/2), μ (frontier (ball x r))=0 := by
    simpa only [thickening_singleton] using
      exists_null_frontier_thickening μ ({x} : Set X) (half_pos positive)
  choose r hr boundary using radii
  obtain ⟨centers,cover⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover
    (fun x => ball x (r x)) (fun _ => isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_ball_self (hr x).1⟩)
  let e : centers ≃ Fin (Fintype.card centers) := Fintype.equivFin centers
  let A : Fin (Fintype.card centers) → Set X := fun i => ball (e.symm i).val (r (e.symm i).val)
  have measurable : ∀ i, MeasurableSet (A i) := fun _ => measurableSet_ball
  have boundaryA : ∀ i, μ (frontier (A i))=0 := fun i => boundary (e.symm i).val
  have coverA : (⋃ i, A i)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y,hy,hx⟩ := mem_iUnion₂.mp (cover (mem_univ x))
    exact mem_iUnion.mpr ⟨e ⟨y,hy⟩,by simpa only [A,Equiv.symm_apply_apply] using hx⟩
  let P : MeasurablePartition (X := X) (Fintype.card centers) :=
    ⟨disjointed A, (fun i => by
      rw [disjointed_eq_inter_compl]
      exact (measurable i).inter (MeasurableSet.iInter (fun j =>
        MeasurableSet.iInter (fun _ => (measurable j).compl)))), disjoint_disjointed A,
      iUnion_disjointed.trans coverA⟩
  refine ⟨_,P,disjointed_frontier_null A μ boundaryA,?_⟩
  intro i x y hx hy
  have nearx := mem_ball.mp (disjointed_subset A i hx)
  have neary := mem_ball.mp (disjointed_subset A i hy)
  have triangle := dist_triangle x (e.symm i).val y
  rw [dist_comm (e.symm i).val y] at triangle
  have small := (hr (e.symm i).val).2
  linarith

end LeanShared.ThermodynamicDefinitions
