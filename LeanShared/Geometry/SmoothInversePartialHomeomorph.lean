module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Smoothness of the inverse of an actual local homeomorphism from a
normed space to a boundaryless manifold, when its actual differential
is bijective. This is proved in a target chart using the ordinary
inverse-function theorem for a preexisting local inverse. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.SmoothInversePartialHomeomorph
variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

set_option backward.isDefEq.respectTransparency false in
theorem smooth_inverse (e : OpenPartialHomeomorph E N)
    (smooth : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ e e.source)
    (differential : ∀ x ∈ e.source, Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) e x)) :
    ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ e.symm e.target := by
  intro y hy
  let x := e.symm y
  let c := chartAt F y
  let f := e.trans c
  have hx : x ∈ e.source := e.map_target hy
  have ex : e x = y := e.right_inv hy
  have cy : y ∈ c.source := mem_chart_source F y
  have ftarget : c y ∈ f.target := by
    refine ⟨c.map_source cy, ?_⟩
    change c.symm (c y) ∈ e.target
    rw [c.left_inv cy]
    exact hy
  have csmooth : ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ c (e x) := by
    rw [ex]
    exact contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas y) cy
  have esmooth : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ e x :=
    (smooth x hx).contMDiffAt (e.open_source.mem_nhds hx)
  have fsmooth : ContDiffAt ℝ ∞ f x := by
    exact (csmooth.comp x esmooth).contDiffAt
  have cdiff : c.MDifferentiable (𝓘(ℝ, F)) (𝓘(ℝ, F)) :=
    ⟨fun z hz => (mdifferentiableAt_atlas (chart_mem_atlas F y) hz).mdifferentiableWithinAt,
      fun z hz => (mdifferentiableAt_atlas_symm (chart_mem_atlas F y) hz).mdifferentiableWithinAt⟩
  have bijective : Function.Bijective (fderiv ℝ f x) := by
    have chain := mfderiv_comp x (csmooth.mdifferentiableAt (by simp)) (esmooth.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at chain
    have composite :=
      (cdiff.mfderiv_bijective (by simpa only [ex] using cy)).comp (differential x hx)
    rw [← ContinuousLinearMap.coe_comp, ← chain] at composite
    exact composite
  let A : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap bijective).toContinuousLinearEquiv
  have derivative : HasFDerivAt f A.toContinuousLinearMap x := by
    simpa only [A] using! (fsmooth.differentiableAt (by simp)).hasFDerivAt
  have inverseSmooth : ContDiffAt ℝ ∞ f.symm (c y) := by
    apply f.contDiffAt_symm ftarget
    · simpa only [f, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, c.left_inv cy] using derivative
    · simpa only [f, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, c.left_inv cy] using fsmooth
  have result : ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ e.symm y := by
    rw [contMDiffAt_iff]
    refine ⟨e.symm.continuousAt hy, ?_⟩
    simpa only [f, c, mfld_simps, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
      using inverseSmooth
  exact result.contMDiffWithinAt

end LeanShared.SmoothInversePartialHomeomorph
