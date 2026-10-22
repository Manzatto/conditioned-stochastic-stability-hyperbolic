module
public import LeanShared.MeasureTheory.CoordinatePatchLocalDensity
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support

/-! A compactly supported coordinate density, transformed by an actual C1
chart transition, has a continuous zero extension throughout the receiving
chart. Compact support excludes any artificial jump at the other chart's
boundary. -/
public noncomputable section
namespace LeanShared.CoordinateJacobianDensity
open Set Filter
open scoped Topology

@[expose] def density
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (e d : OpenPartialHomeomorph M E) (p : E → ℝ) : E → ℝ := by
  classical
  exact fun y => if y ∈ (e.symm.trans d).target then
    |(fderiv ℝ (e.symm.trans d).symm y).det| * p ((e.symm.trans d).symm y) else 0

set_option maxHeartbeats 1600000 in
theorem continuousOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M]
    (e d : OpenPartialHomeomorph M E) (p : E → ℝ)
    (smooth : ContDiffOn ℝ 1 (e.symm.trans d).symm (e.symm.trans d).target)
    (continuous : Continuous p) (compact : HasCompactSupport p)
    (support : tsupport p ⊆ e.target) : ContinuousOn (density e d p) d.target := by
  classical
  let A := e.symm.trans d
  let K := e.symm '' tsupport p
  have compactK : IsCompact K := compact.isCompact.image_of_continuousOn
    (e.symm.continuousOn.mono support)
  have insideK : K ⊆ e.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_target (support hx)
  intro y hy
  by_cases inside : y ∈ A.target
  · have regular : ContDiffAt ℝ 1 A.symm y :=
      (smooth y inside).contDiffAt (A.open_target.mem_nhds inside)
    have determinant : ContinuousAt (fun z => (fderiv ℝ A.symm z).det) y :=
      ContinuousLinearMap.continuous_det.continuousAt.comp (regular.continuousAt_fderiv (by norm_num))
    have product := determinant.abs.mul (continuous.continuousAt.comp regular.continuousAt)
    apply ContinuousAt.continuousWithinAt
    apply product.congr_of_eventuallyEq
    filter_upwards [A.open_target.mem_nhds inside] with z hz
    change (if z ∈ A.target then |(fderiv ℝ A.symm z).det| * p (A.symm z) else 0) = _
    exact ite_eq_left hz
  · have outside : d.symm y ∉ K := by
      intro member
      apply inside
      exact ⟨hy,insideK member⟩
    have near : ∀ᶠ z in 𝓝 y, z ∈ d.target ∧ d.symm z ∉ K :=
      Filter.Eventually.and (d.open_target.mem_nhds hy)
        ((d.continuousAt_symm hy).preimage_mem_nhds (compactK.isClosed.isOpen_compl.mem_nhds outside))
    have zero : density e d p =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [near] with z hz
      by_cases member : z ∈ A.target
      · have point : d.symm z ∈ e.source := member.2
        have vanish : p (e (d.symm z)) = 0 := by
          by_contra nonzero
          have belongs : e (d.symm z) ∈ tsupport p :=
            subset_closure (Function.mem_support.mpr nonzero)
          exact hz.2 ⟨e (d.symm z),belongs,e.left_inv point⟩
        change (if z ∈ A.target then |(fderiv ℝ A.symm z).det| * p (A.symm z) else 0) = 0
        rw [ite_eq_left member]
        change |(fderiv ℝ A.symm z).det| * p (e (d.symm z)) = 0
        rw [vanish,mul_zero]
      · change (if z ∈ A.target then |(fderiv ℝ A.symm z).det| * p (A.symm z) else 0) = 0
        exact ite_eq_right member
    exact continuousAt_const.congr_of_eventuallyEq zero |>.continuousWithinAt

end LeanShared.CoordinateJacobianDensity
