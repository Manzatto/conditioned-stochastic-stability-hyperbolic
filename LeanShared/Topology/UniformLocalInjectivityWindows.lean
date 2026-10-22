module
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import LeanShared.Geometry.CompactUniformCenteredCharts
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! Pointwise open injectivity windows for a family on a compact space give
one spatial radius and one parameter window valid at every point. -/
public noncomputable section
namespace LeanShared.UniformLocalInjectivityWindows
open Set
open scoped NNReal

theorem exists_window
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (Ω : ℝ≥0 → Type*) (f : ∀ ε, Ω ε → X → X)
    (localWindows : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∀ ε, 0 < ε → ε ≤ η → ∀ a, InjOn (f ε a) U) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε, 0 < ε → ε ≤ η → ∀ a x y,
        dist x y < radius → f ε a x = f ε a y → x = y := by
  classical
  choose U openU member window positiveWindow injective using localWindows
  obtain ⟨centers,cover⟩ := isCompact_univ.elim_finite_subcover U openU
    (fun x _ => mem_iUnion.mpr ⟨x,member x⟩)
  have cover' : (univ : Set X) ⊆ ⋃ i : centers, U i.val := by
    intro x hx
    obtain ⟨i,hi,inside⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,inside⟩
  obtain ⟨radius,positiveRadius,balls⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i : centers => openU i.val) cover'
  obtain ⟨η,positiveη,common⟩ := LeanShared.CompactUniformCenteredCharts.common_positive centers
    (fun i => (window i : ℝ)) (fun i _ => positiveWindow i)
  refine ⟨radius,positiveRadius,⟨η,positiveη.le⟩,positiveη,fun ε hp hw a x y close equal => ?_⟩
  obtain ⟨i,ballInside⟩ := balls x (mem_univ x)
  have parameter : ε ≤ window i.val := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr hw).trans (common i.val i.property))
  apply injective i.val ε hp parameter a
  · exact ballInside (Metric.mem_ball_self positiveRadius)
  · exact ballInside (by simpa only [Metric.mem_ball,dist_comm] using close)
  · exact equal

end LeanShared.UniformLocalInjectivityWindows
