module

public import LeanShared.Dynamics.IsolatingNeighborhood
public import Mathlib.Topology.MetricSpace.Closeds

/-! A closed two-point relation which separates entire bilateral orbits
already separates a finite uniform window on a compact metric space.
This covers consecutive-block generators without changing the metric. -/
public noncomputable section
open Set Function
namespace LeanShared.ClosedRelationFiniteDetection
variable {X : Type*} [MetricSpace X] [CompactSpace X]

def window (T : X ≃ₜ X) (R : Set (X × X)) (n : ℕ) : Set (X × X) :=
  {z | ∀ j ≤ n, (T^[j] z.1, T^[j] z.2) ∈ R ∧
    ((T.symm : X → X)^[j] z.1, (T.symm : X → X)^[j] z.2) ∈ R}

theorem exists_finite_detection (T : X ≃ₜ X) (R : Set (X × X)) (closed : IsClosed R)
    (separates : ∀ x y, (∀ j : ℕ, (T^[j] x, T^[j] y) ∈ R ∧
      ((T.symm : X → X)^[j] x, (T.symm : X → X)^[j] y) ∈ R) → x = y)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y, (x, y) ∈ window T R N → dist x y < ε := by
  have closedWindow (n : ℕ) : IsClosed (window T R n) := by
    have same : window T R n = ⋂ j : ℕ, ⋂ (_ : j ≤ n),
        ((fun z : X × X => (T^[j] z.1, T^[j] z.2)) ⁻¹' R) ∩
        ((fun z : X × X => ((T.symm : X → X)^[j] z.1,
          (T.symm : X → X)^[j] z.2)) ⁻¹' R) := by
      ext z
      simp only [window, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage]
    rw [same]
    exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      (closed.preimage (((T.continuous.iterate j).comp continuous_fst).prodMk
        ((T.continuous.iterate j).comp continuous_snd))).inter
      (closed.preimage (((T.symm.continuous.iterate j).comp continuous_fst).prodMk
        ((T.symm.continuous.iterate j).comp continuous_snd)))))
  have antitone : Antitone (window T R) := by
    intro n m h z hz j hj
    exact hz j (hj.trans h)
  have intersection : (⋂ n, window T R n) ⊆ {z : X × X | dist z.1 z.2 < ε} := by
    intro z hz
    have same := separates z.1 z.2 (fun j => (mem_iInter.mp hz j) j le_rfl)
    change dist z.1 z.2 < ε
    simpa only [same, dist_self] using positive
  obtain ⟨N, positiveN, subset⟩ := exists_pos_tail_subset_open
    ((closedWindow 0).isCompact) closedWindow antitone
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const) intersection
  exact ⟨N, positiveN, fun x y member => subset member⟩

end LeanShared.ClosedRelationFiniteDetection
