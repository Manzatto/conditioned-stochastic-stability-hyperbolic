module
public import LeanShared.Analysis.RestrictedInverseJacobianBound
public import LeanShared.Analysis.LocalInverseDerivative
public import LeanShared.Analysis.LocalInverseWord

/-! The actual C1 inverse of a local diffeomorphism supplies a coarse
uniform reciprocal tangent-Jacobian bound on every leaf plane. -/
public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace LeanShared.LocalDiffeomorphismCoarseJacobian
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem inverse_derivative (F:OpenPartialHomeomorph E E)
    (forward:ContDiffOn ℝ 1 F F.source) (backward:ContDiffOn ℝ 1 F.symm F.target)
    {x:E} (inside:x∈F.source):
    ∃A:E≃L[ℝ] E,HasFDerivAt F A.toContinuousLinearMap x ∧
      HasFDerivAt F.symm A.symm.toContinuousLinearMap (F x):=by
  have hf:DifferentiableAt ℝ F x:=((forward.differentiableOn one_ne_zero) x inside).differentiableAt
    (F.open_source.mem_nhds inside)
  have hb:DifferentiableAt ℝ F.symm (F x):=
    ((backward.differentiableOn one_ne_zero) (F x) (F.map_source inside)).differentiableAt
      (F.open_target.mem_nhds (F.map_source inside))
  have injective:Function.Injective (fderiv ℝ F x):=by
    apply FiniteDerivativeWord.fderiv_injective_of_local_inverse F F.symm x hf hb
    filter_upwards [F.open_source.mem_nhds inside] with y hy
    exact F.left_inv hy
  let A:E≃L[ℝ] E:=(LinearEquiv.ofInjectiveEndo (fderiv ℝ F x).toLinearMap injective).toContinuousLinearEquiv
  have derivative:HasFDerivAt F A.toContinuousLinearMap x:=hf.hasFDerivAt
  refine ⟨A,derivative,?_⟩
  apply LocalInverseDerivative.hasFDerivAt F F.symm (F x) A
    (by simpa only [F.left_inv inside] using derivative) hb
  filter_upwards [F.open_target.mem_nhds (F.map_source inside)] with y hy
  exact F.right_inv hy

theorem bound (F:OpenPartialHomeomorph E E)
    (forward:ContDiffOn ℝ 1 F F.source) (backward:ContDiffOn ℝ 1 F.symm F.target)
    {x:E} (inside:x∈F.source) (W:Submodule ℝ E) {K:ℝ} (nonnegative:0≤K)
    (inverse:‖fderiv ℝ F.symm (F x)‖≤K):
    1≤GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ W)) K*
      ((fderiv ℝ F x).toLinearMap.domRestrict W).normDet:=by
  obtain ⟨A,derivative,inverseDerivative⟩:=inverse_derivative F forward backward inside
  rw [derivative.fderiv]
  apply RestrictedInverseJacobianBound.bound A W nonnegative
  rw [←inverseDerivative.fderiv]
  exact inverse

theorem uniform_bound (F : OpenPartialHomeomorph E E)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    {x : E} (inside : x ∈ F.source) (W : Submodule ℝ E) {K : ℝ} (nonnegative : 0 ≤ K)
    (inverse : ‖fderiv ℝ F.symm (F x)‖ ≤ K) :
    1 ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K *
      ((fderiv ℝ F x).toLinearMap.domRestrict W).normDet := by
  have smaller := bound F forward backward inside W nonnegative inverse
  have dimensions : Module.finrank ℝ W ≤ Module.finrank ℝ E := Submodule.finrank_le W
  have density : GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ W)) K ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K := by
    simp only [GraphJacobian.densityBound, Fintype.card_fin]
    apply Real.sqrt_le_sqrt
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le dimensions
    · exact pow_le_pow_right₀ (by nlinarith [sq_nonneg K]) dimensions
    · positivity
    · positivity
  exact smaller.trans (mul_le_mul_of_nonneg_right density (LinearMap.normDet_nonneg _))
end LeanShared.LocalDiffeomorphismCoarseJacobian
