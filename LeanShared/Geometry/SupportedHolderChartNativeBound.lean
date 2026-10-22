module
public import LeanShared.Geometry.SupportedHolderChartSpace
public import LeanShared.Geometry.BoundedRiemannianChartLipschitz
public import LeanShared.Analysis.CompactScaledLocalHolder
import Mathlib.Tactic.Ring

/-! A supported coordinate Holder function has a quantitative native Holder
bound for the actual bounded Riemannian length metric. The bound is linear
in its coordinate graph norm, uniformly over ALL supported functions. -/
public noncomputable section
namespace LeanShared.SupportedHolderChartSpace
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction

set_option maxHeartbeats 2400000 in
theorem native_increment_bound
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {b : ℝ} (hb : 0 ≤ b) {K : Set E} (hK : IsCompact K)
    (e : OpenPartialHomeomorph M E) (target : K ⊆ e.target)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : space (a := b) K) (x y : M),
      ‖realization hK e target v x-realization hK e target v y‖ ≤ C*‖v‖*dist x y^b := by
  classical
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let F := fun (v : space (a := b) K) (x : M) => realization hK e target v x
  have value (v : space (a := b) K) (x : M) : ‖F v x‖ ≤ ‖v‖ :=
    ((realization hK e target v).norm_coe_le_norm x).trans (norm_physical hK e target v)
  have agrees (v : space (a := b) K) (x : M) (hx : x ∈ e.source) :
      F v x = BoundedHolderSpace.physical E b v.val (e x) := by
    change (if x ∈ e.source then _ else 0) = _
    exact ite_eq_left hx
  have localBound : ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ v : space (a := b) K, (∀ y ∈ W, ‖F v y‖ ≤ B*‖v‖) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖F v y-F v z‖ ≤ C*‖v‖*dist y z^b := by
    intro x
    by_cases source : x ∈ e.source
    · obtain ⟨W,openW,inW,insideW,L,lip⟩ := BoundedRiemannianMetric.chart_local_lipschitz e he x source
      refine ⟨W,openW,inW,1,(L:ℝ)^b,zero_le_one,Real.rpow_nonneg L.coe_nonneg _,fun v => ⟨?_,?_⟩⟩
      · intro y _
        simpa only [one_mul] using value v y
      · intro y hy z hz
        rw [agrees v y (insideW hy),agrees v z (insideW hz)]
        have increment := BoundedHolderSpace.increment_bound E b v.val (e y) (e z)
        change _ ≤ ‖v‖*dist (e y) (e z)^b at increment
        have power := Real.rpow_le_rpow dist_nonneg (lip y hy z hz) hb
        rw [Real.mul_rpow L.coe_nonneg dist_nonneg] at power
        exact (increment.trans (mul_le_mul_of_nonneg_left power (norm_nonneg v))).trans_eq (by ring)
    · let Q := e.symm '' K
      have compactQ : IsCompact Q := hK.image_of_continuousOn (e.continuousOn_symm.mono target)
      have outside : x ∉ Q := by
        rintro ⟨y,hy,rfl⟩
        exact source (e.map_target (target hy))
      have vanish (v : space (a := b) K) (y : M) (hy : y ∈ Qᶜ) : F v y = 0 := by
        by_contra nonzero
        exact hy ((realization_support hK e target v) (subset_tsupport (F v) nonzero))
      refine ⟨Qᶜ,compactQ.isClosed.isOpen_compl,outside,0,0,le_rfl,le_rfl,fun v => ⟨?_,?_⟩⟩
      · intro y hy
        rw [vanish v y hy,norm_zero,zero_mul]
      · intro y hy z hz
        rw [vanish v y hy,vanish v z hz,sub_self,norm_zero,zero_mul,zero_mul]
  obtain ⟨B,C,_,hC,bound⟩ := CompactUniformLocalHolder.scaled_bounds F (fun v => ‖v‖)
    (fun v => norm_nonneg v) b hb localBound
  exact ⟨C,hC,fun v x y => (bound v).2 x y⟩

end LeanShared.SupportedHolderChartSpace
