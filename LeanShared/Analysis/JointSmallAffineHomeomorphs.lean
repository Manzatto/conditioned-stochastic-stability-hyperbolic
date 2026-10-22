module
public import LeanShared.Analysis.ParametricGlobalInverseRegularity

/-! A jointly C1 family with an actual uniformly small affine residual
constructs global homeomorphisms on an open parameter domain and proves
joint C1 regularity of their genuine inverses. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace LeanShared.JointSmallAffineHomeomorphs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_family (A : E ≃L[ℝ] E) (b : E) (f : P × E → E)
    (O : Set P) (openO : IsOpen O) (joint : ContDiffOn ℝ 1 f (O ×ˢ univ))
    (k : ℝ≥0) (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (close : ∀ p ∈ O, ∀ x, ‖fderiv ℝ (fun z => f (p,z)) x-A.toContinuousLinearMap‖ ≤ k) :
    ∃ H : P → E ≃ₜ E, (∀ p ∈ O, ∀ x, H p x = f (p,x)) ∧
      ContDiffOn ℝ 1 (fun q : P × E => H q.1 q.2) (O ×ˢ univ) ∧
      ContDiffOn ℝ 1 (fun q : P × E => (H q.1).symm q.2) (O ×ˢ univ) := by
  classical
  let u (p : P) (x : E) := f (p,x)-(A x+b)
  have smoothFiber (p : P) (hp : p ∈ O) : ContDiff ℝ 1 (fun x => f (p,x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact ((joint (p,x) ⟨hp,mem_univ _⟩).contDiffAt
      ((openO.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
  have du (p : P) (hp : p ∈ O) : Differentiable ℝ (u p) :=
    (smoothFiber p hp |>.differentiable (by norm_num)).sub (A.differentiable.add_const b)
  have lip (p : P) (hp : p ∈ O) : LipschitzWith k (u p) := by
    apply SmallAffinePerturbation.lipschitz_of_derivative (du p hp)
    intro x
    have actual := ((smoothFiber p hp |>.differentiable (by norm_num) x).hasFDerivAt.sub
      (A.hasFDerivAt.add_const b)).fderiv
    change ‖fderiv ℝ ((fun z => f (p,z))-(fun z => A z+b)) x‖ ≤ k
    rw [actual]
    exact close p hp x
  let H : P → E ≃ₜ E := fun p => if hp : p ∈ O then
    SmallAffinePerturbation.homeomorph A b (lip p hp) small else A.toHomeomorph
  have actual (p : P) (hp : p ∈ O) (x : E) : H p x = f (p,x) := by
    dsimp only [H]
    rw [dite_eq_left hp, SmallAffinePerturbation.homeomorph_apply]
    dsimp only [SmallAffinePerturbation.map,u]
    abel
  refine ⟨H,actual,?_,?_⟩
  · exact joint.congr (fun q hq => actual q.1 hq.1 q.2)
  · intro q hq
    let p := q.1
    let x := (H p).symm q.2
    let D := SmallAffinePerturbation.derivativeEquiv A b (lip p hq.1) small (du p hq.1) x
    have raw : HasFDerivAt (SmallAffinePerturbation.map A b (u p)) D.toContinuousLinearMap x := by
      change HasFDerivAt (SmallAffinePerturbation.map A b (u p))
        (SmallAffinePerturbation.derivativeEquiv A b (lip p hq.1) small (du p hq.1) x).toContinuousLinearMap x
      rw [SmallAffinePerturbation.derivativeEquiv_coe]
      exact ((A.differentiable.add_const b).add (du p hq.1) x).hasFDerivAt
    have mapEq : SmallAffinePerturbation.map A b (u p) = fun z => f (p,z) := by
      funext z
      dsimp only [SmallAffinePerturbation.map,u]
      abel
    rw [mapEq] at raw
    have smooth := (joint (p,x) ⟨hq.1,mem_univ _⟩).contDiffAt
      ((openO.prod isOpen_univ).mem_nhds ⟨hq.1,mem_univ _⟩)
    have near : ∀ᶠ a in 𝓝 p, ∀ z, H a z = f (a,z) := by
      filter_upwards [openO.mem_nhds hq.1] with a ha
      exact actual a ha
    have inverse := ParametricGlobalInverseRegularity.contDiffAt_inverse_family f H p x
      (by norm_num : (1 : ℕ∞ω) ≠ 0) smooth D raw near
    have image : f (p,x) = q.2 := (actual p hq.1 x).symm.trans ((H p).apply_symm_apply q.2)
    rw [image] at inverse
    exact inverse.contDiffWithinAt

end LeanShared.JointSmallAffineHomeomorphs
