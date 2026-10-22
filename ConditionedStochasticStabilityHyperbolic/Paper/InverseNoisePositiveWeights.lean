module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformWindow
public import LeanShared.Topology.CompactNearDiagonalContinuity

/-! Positivity of the ORIGINAL inverse departure weight on a compact
collar follows from its deterministic two-sided positivity and the derived
inverse continuity modulus. No linear inverse Whitney estimate is assumed. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal

 theorem InverseFamily.eventually_positive_weight
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (w : M → ℝ) (continuous : Continuous w)
    (G : Set M) (positive : ∀ x ∈ closure G, 0 < w (T.symm x)) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ a : cube (ι := ι) ε, ∀ x ∈ G, 0 < w (J.map ε (a.val,x)) := by
  let U := {x : M | 0 < w x}
  have openU : IsOpen U := isOpen_lt continuous_const continuous
  have compact : IsCompact (T.symm '' closure G) := isClosed_closure.isCompact.image T.symm.continuous
  have inside : T.symm '' closure G ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    exact positive x hx
  obtain ⟨δ,hδ,near⟩ := LeanShared.CompactNearDiagonalContinuity.exists_radius
    (T.symm '' closure G) U compact openU inside (id : M → M) continuous_id.continuousOn 1 (by norm_num)
  obtain ⟨η,hη,_,close⟩ := F.inverse_uniform_window δ hδ
  refine ⟨min J.window η,lt_min J.positive hη,min_le_left _ _,fun ε hp hw a x hx => ?_⟩
  have closeInverse := close ε hp (hw.trans (min_le_right _ _)) a
    (fun y => J.map ε (a.val,y))
    (J.right ε hp (hw.trans (min_le_left _ _)) a.val
      (J.contains ε hp (hw.trans (min_le_left _ _)) a.property)) x
  exact (near (T.symm x) ⟨x,subset_closure hx,rfl⟩ _
    (by simpa only [dist_comm] using closeInverse)).1

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
