module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.UniformSpace.Equiv

/-! A globally small derivative perturbation of an actual invertible affine
map constructs an actual global homeomorphism. Every actual differential
is invertible, so the genuine inverse retains ordinary smoothness. -/
@[expose] public noncomputable section
open Set Function
open scoped NNReal ContDiff Topology
namespace LeanShared.SmallAffinePerturbation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def map (A : E ≃L[ℝ] F) (b : F) (u : E → F) (x : E) : F := A x + b + u x

omit [CompleteSpace E] in
theorem approximates (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) : ApproximatesLinearOn (map A b u) A.toContinuousLinearMap univ k := by
  intro x _ y _
  have same : map A b u x - map A b u y - A (x-y) = u x-u y := by
    simp only [map, map_sub]
    abel
  change ‖map A b u x - map A b u y - A (x-y)‖ ≤ (k : ℝ) * ‖x-y‖
  rw [same]
  exact lip.norm_sub_le x y

/-- This includes zero-dimensional spaces without a nontriviality input. -/
def homeomorph (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u)
    (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹) : E ≃ₜ F :=
  (approximates A b lip).toHomeomorph (map A b u) small

theorem homeomorph_apply (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (x : E) : homeomorph A b lip small x = map A b u x := rfl

omit [CompleteSpace E] in
/-- A derivative bound supplies the Lipschitz hypothesis through the actual
mean-value theorem on the whole convex model space. -/
theorem lipschitz_of_derivative {u : E → F} {k : ℝ≥0} (du : Differentiable ℝ u)
    (bound : ∀ x, ‖fderiv ℝ u x‖ ≤ k) : LipschitzWith k u :=
  lipschitzWith_of_nnnorm_fderiv_le du (fun x => bound x)

omit [CompleteSpace E] in
theorem hasFDerivAt_map (A : E ≃L[ℝ] F) (b : F) {u : E → F}
    (du : Differentiable ℝ u) (x : E) :
    HasFDerivAt (map A b u) (A.toContinuousLinearMap + fderiv ℝ u x) x :=
  (A.hasFDerivAt.add_const b).add (du x).hasFDerivAt

/-- The actual derivative is bijective; no invertible-derivative packet is
supplied as an additional hypothesis. -/
theorem derivative_bijective (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (du : Differentiable ℝ u) (x : E) : Function.Bijective (fderiv ℝ (map A b u) x) := by
  rw [(hasFDerivAt_map A b du x).fderiv]
  have close : ApproximatesLinearOn (A.toContinuousLinearMap + fderiv ℝ u x)
      A.toContinuousLinearMap univ k := by
    intro y _ z _
    have same : (A.toContinuousLinearMap + fderiv ℝ u x) y -
        (A.toContinuousLinearMap + fderiv ℝ u x) z - A (y-z) = (fderiv ℝ u x) (y-z) := by
      simp only [add_apply, ContinuousLinearEquiv.coe_coe, map_sub]
      abel
    change ‖(A.toContinuousLinearMap + fderiv ℝ u x) y -
      (A.toContinuousLinearMap + fderiv ℝ u x) z - A (y-z)‖ ≤ (k : ℝ) * ‖y-z‖
    rw [same]
    exact (fderiv ℝ u x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ lip) _
  exact ⟨injOn_univ.mp (close.injOn small), close.surjective small⟩

def derivativeEquiv (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (du : Differentiable ℝ u) (x : E) : E ≃L[ℝ] F := by
  let e : E ≃ᵤ F := {
    A.toEquiv with
    uniformContinuous_toFun := A.toContinuousLinearMap.lipschitzWith.uniformContinuous
    uniformContinuous_invFun := A.symm.toContinuousLinearMap.lipschitzWith.uniformContinuous }
  let : CompleteSpace F := e.completeSpace_iff.mp inferInstance
  exact ContinuousLinearEquiv.ofBijective (fderiv ℝ (map A b u) x)
    (LinearMap.ker_eq_bot.mpr (derivative_bijective A b lip small du x).1)
    (LinearMap.range_eq_top.mpr (derivative_bijective A b lip small du x).2)

theorem derivativeEquiv_coe (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (du : Differentiable ℝ u) (x : E) :
    (derivativeEquiv A b lip small du x).toContinuousLinearMap = fderiv ℝ (map A b u) x := by
  simp only [derivativeEquiv, ContinuousLinearEquiv.coe_ofBijective]

omit [CompleteSpace E] in
theorem contDiff_map (A : E ≃L[ℝ] F) (b : F) {u : E → F} {n : ℕ∞ω}
    (smooth : ContDiff ℝ n u) : ContDiff ℝ n (map A b u) :=
  (A.contDiff.add contDiff_const).add smooth

theorem contDiff_inverse (A : E ≃L[ℝ] F) (b : F) {u : E → F} {k : ℝ≥0}
    (lip : LipschitzWith k u) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (du : Differentiable ℝ u) {n : ℕ∞ω} (smooth : ContDiff ℝ n u) :
    ContDiff ℝ n (homeomorph A b lip small).symm := by
  apply Homeomorph.contDiff_symm (f₀' := derivativeEquiv A b lip small du)
  · intro x
    change HasFDerivAt (map A b u) _ x
    rw [derivativeEquiv_coe]
    exact ((A.differentiable.add_const b).add du x).hasFDerivAt
  · exact contDiff_map A b smooth

end LeanShared.SmallAffinePerturbation
