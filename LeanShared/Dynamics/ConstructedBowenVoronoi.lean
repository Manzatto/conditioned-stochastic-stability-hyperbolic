module

public import LeanShared.Dynamics.BowenVoronoiPartition
public import LeanShared.Dynamics.SeparatedSpanningSet
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality

/-! Compact expansive dynamics construct actual finite Bowen/Voronoi
partitions at every horizon. No centers, finite cover, partition, or
fine-ball inclusion is supplied as a source premise. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1000000 in
theorem exists_bowen_voronoi (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ε : ℝ) (positive : 0 < ε) (n : ℕ) :
    ∃ k : ℕ, ∃ positiveK : 0 < k, ∃ centers : Fin k → X,
      let Q := bowenVoronoiPartition T T.continuous centers positiveK n
      (∀ i x, x ∈ Q.atom i → ∀ j ≤ n, dist (T^[j] x) (T^[j] (centers i)) < ε) ∧
      (∀ i x, (∀ j ≤ n, dist (T^[j] x) (T^[j] (centers i)) < ε / 3) → x ∈ Q.atom i) ∧
      (∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i →
        ∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 2 * ε) := by
  classical
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts ε positive
  obtain ⟨s, nonempty, separated, spans⟩ := exists_separated_spanning T (n + 1) ε positive
    (a ^ (n + 1 + p)) (count (n + 1))
  let : Nonempty s := nonempty.to_subtype
  let e := Fintype.equivFin s
  let centers : Fin (Fintype.card s) → X := fun i => (e.symm i).val
  have positiveK : 0 < Fintype.card s := Fintype.card_pos
  have spanning : ∀ x, ∃ i, FiniteBowenDistance.distance T n x (centers i) < ε := by
    intro x
    obtain ⟨y, hy, near⟩ := spans x
    refine ⟨e ⟨y, hy⟩, ?_⟩
    apply (FiniteBowenDistance.lt_iff T n x _ ε).mpr
    intro j hj
    have same : centers (e ⟨y, hy⟩) = y := by simp only [centers, Equiv.symm_apply_apply]
    rw [same]
    exact near j (by omega)
  have apart : ∀ i j, i ≠ j → ε ≤ FiniteBowenDistance.distance T n (centers i) (centers j) := by
    intro i j different
    have notEqual : centers i ≠ centers j := by
      intro equal
      exact different (e.symm.injective (Subtype.ext equal))
    obtain ⟨r, hr, bound⟩ := separated.2 (centers i) (e.symm i).property
      (centers j) (e.symm j).property notEqual
    exact bound.trans (FiniteBowenDistance.coordinate_le T n _ _ ⟨r, hr⟩)
  refine ⟨Fintype.card s, positiveK, centers, ?_, ?_, ?_⟩
  · intro i x member
    exact (FiniteBowenDistance.lt_iff T n x _ ε).mp
      (bowenVoronoi_atom_bound T T.continuous centers positiveK n ε spanning i x member)
  · intro i x near
    exact bowenVoronoi_ball_mem T T.continuous centers positiveK n ε positive apart i x
      ((FiniteBowenDistance.lt_iff T n x _ _).mpr near)
  · exact bowenVoronoi_atom_mesh T T.continuous centers positiveK n ε spanning

end LeanShared.ThermodynamicDefinitions
