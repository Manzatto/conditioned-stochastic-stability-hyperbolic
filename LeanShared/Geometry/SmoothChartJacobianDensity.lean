module
public import LeanShared.MeasureTheory.CoordinateJacobianDensity
public import LeanShared.Analysis.SmoothDeterminant
public import LeanShared.Geometry.ChartTransitionJacobian
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Smooth zero extensions of actual transition-Jacobian chart densities.
Compact support removes the apparent boundary of the source chart. -/
public noncomputable section
namespace LeanShared.CoordinateJacobianDensity
open Set Filter IsManifold
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem contDiffOn_of_transition
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M]
    (e d : OpenPartialHomeomorph M E) (p : E → ℝ)
    (smooth : ContDiffOn ℝ ∞ (e.symm.trans d).symm (e.symm.trans d).target)
    (nonzero : ∀ y ∈ (e.symm.trans d).target,
      (fderiv ℝ (e.symm.trans d).symm y).det ≠ 0)
    (regularP : ContDiff ℝ ∞ p) (compact : HasCompactSupport p)
    (support : tsupport p ⊆ e.target) : ContDiffOn ℝ ∞ (density e d p) d.target := by
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
  · have regular : ContDiffAt ℝ ∞ A.symm y :=
      (smooth y inside).contDiffAt (A.open_target.mem_nhds inside)
    have determinant : ContDiffAt ℝ ∞ (fun z => (fderiv ℝ A.symm z).det) y :=
      SmoothDeterminant.contDiff.contDiffAt.comp y (regular.fderiv_right (by simp))
    have product := (determinant.abs (nonzero y inside)).mul
      (regularP.contDiffAt.comp y regular)
    apply ContDiffAt.contDiffWithinAt
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
    exact contDiffAt_const.congr_of_eventuallyEq zero |>.contDiffWithinAt


theorem contDiffOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (e d : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (p : E → ℝ) (regularP : ContDiff ℝ ∞ p) (compact : HasCompactSupport p)
    (support : tsupport p ⊆ e.target) : ContDiffOn ℝ ∞ (density e d p) d.target := by
  have raw : ContMDiffOn (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (e ∘ d.symm) (e.symm.trans d).target :=
    (contMDiffOn_of_mem_maximalAtlas he).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hd).mono (fun _ h => h.1)) (fun _ h => h.2)
  have smooth : ContDiffOn ℝ ∞ (e.symm.trans d).symm (e.symm.trans d).target := by
    simpa only [OpenPartialHomeomorph.coe_trans_symm,OpenPartialHomeomorph.symm_symm] using raw.contDiffOn
  exact contDiffOn_of_transition e d p smooth
    (ChartTransitionJacobian.inverse_det_ne_zero e d he hd) regularP compact support

end LeanShared.CoordinateJacobianDensity
