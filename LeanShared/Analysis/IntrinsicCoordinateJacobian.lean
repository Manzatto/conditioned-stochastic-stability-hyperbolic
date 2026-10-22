module
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-! The intrinsic rectangular Jacobian is continuous and obeys the ordinary
coordinate-change law for actual differentiable parametrizations. -/
public noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace LeanShared.IntrinsicCoordinateJacobian
variable {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_normDet : Continuous (fun L : U →L[ℝ] E => L.toLinearMap.normDet) := by
  let b := stdOrthonormalBasis ℝ U
  have equal (L : U →L[ℝ] E) : L.toLinearMap.normDet =
      Real.sqrt (Matrix.gram ℝ (fun i => L (b i))).det := by
    have sq : (Matrix.gram ℝ (fun i => L (b i))).det = L.toLinearMap.normDet ^ 2 :=
      (LinearMap.normDet_sq_eq_det_gram L.toLinearMap b).symm
    rw [sq, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  have matrixContinuous : Continuous
      (fun L : U →L[ℝ] E => Matrix.gram ℝ (fun i => L (b i))) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun L : U →L[ℝ] E => inner ℝ (L (b i)) (L (b j)))
    fun_prop
  simpa only [equal, Function.comp_def] using Real.continuous_sqrt.comp matrixContinuous.matrix_det

theorem continuousOn_jacobian {p : U → E} {s : Set U}
    (smooth : ContDiffOn ℝ 1 p s) (hs : IsOpen s) :
    ContinuousOn (fun x => (fderiv ℝ p x).toLinearMap.normDet) s :=
  continuous_normDet.comp_continuousOn (smooth.continuousOn_fderiv_of_isOpen hs le_rfl)

theorem coordinate_change {p q : U → E} (e : OpenPartialHomeomorph U U)
    (he : DifferentiableOn ℝ e e.source) (hq : DifferentiableOn ℝ q e.target)
    (agrees : ∀ x ∈ e.source, p x = q (e x)) {x : U} (hx : x ∈ e.source) :
    (fderiv ℝ p x).toLinearMap.normDet =
      (fderiv ℝ q (e x)).toLinearMap.normDet * |(fderiv ℝ e x).det| := by
  have nearby : p =ᶠ[𝓝 x] q ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact agrees y hy
  rw [nearby.fderiv_eq, fderiv_comp x
    ((hq (e x) (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
    ((he x hx).differentiableAt (e.open_source.mem_nhds hx))]
  change ((fderiv ℝ q (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap).normDet = _
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ rfl, LinearMap.normDet_eq_abs_det]
end LeanShared.IntrinsicCoordinateJacobian
