module
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic.Linarith

/-! An actual approximate backward orbit uniformly near a set admits a
nearby reference sequence in that set with any prescribed pseudo-orbit error.
The spatial tolerance precedes the set and the whole orbit; no shadowing or
plaque conclusion is an assumption. -/
public noncomputable section
namespace LeanShared.PseudoOrbitReferenceSelection
open Set

 theorem exists_reference_radius
    {X : Type*} [PseudoMetricSpace X] (H : X → X) (continuous : UniformContinuous H)
    (ε cap : ℝ) (positiveε : 0 < ε) (positiveCap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ cap ∧ ∀ Λ : Set X, ∀ b : ℕ → X,
      (∀ n, b n ∈ Metric.thickening δ Λ) →
      (∀ n, dist (H (b (n + 1))) (b n) < ε / 3) →
      ∃ reference : ℕ → Λ, (∀ n, dist (reference n).val (b n) < δ) ∧
        ∀ n, dist (H (reference (n + 1)).val) (reference n).val < ε := by
  obtain ⟨η,positiveη,uniform⟩ := Metric.uniformContinuous_iff.mp continuous (ε / 3) (by positivity)
  let δ := min cap (min η (ε / 3))
  have positiveδ : 0 < δ := lt_min positiveCap (lt_min positiveη (by positivity))
  refine ⟨δ,positiveδ,min_le_left _ _,fun Λ b nearby error => ?_⟩
  have witnesses (n : ℕ) : ∃ x ∈ Λ, dist (b n) x < δ := Metric.mem_thickening_iff.mp (nearby n)
  choose point member close using witnesses
  let reference : ℕ → Λ := fun n => ⟨point n,member n⟩
  have near (n : ℕ) : dist (reference n).val (b n) < δ := by
    simpa only [reference,dist_comm] using close n
  refine ⟨reference,near,fun n => ?_⟩
  have first : dist (H (reference (n + 1)).val) (H (b (n + 1))) < ε / 3 :=
    uniform ((near (n + 1)).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have last : dist (b n) (reference n).val < ε / 3 :=
    (close n).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have triangle := (dist_triangle (H (reference (n + 1)).val) (H (b (n + 1))) (reference n).val).trans
    (add_le_add le_rfl (dist_triangle (H (b (n + 1))) (b n) (reference n).val))
  linarith [error n]

end LeanShared.PseudoOrbitReferenceSelection
