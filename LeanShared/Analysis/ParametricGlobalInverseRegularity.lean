module
public import LeanShared.Analysis.ContDiffLocalLeftInverse
public import LeanShared.Analysis.ParametricInverseDerivative
public import LeanShared.Analysis.SmallAffineInverseBounds

/-! Actual globally bijective fiber maps have a jointly regular inverse
where their forward family is jointly regular and its actual spatial
differential is invertible. No regularity of the inverse family is assumed. -/
public noncomputable section
open Set Filter Function
open scoped Topology ContDiff NNReal
namespace LeanShared.ParametricGlobalInverseRegularity
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

set_option maxHeartbeats 1600000 in
theorem contDiffAt_inverse_family (F : P × E → E) (H : P → E ≃ₜ E)
    (p : P) (x : E) {n : ℕ∞ω} (nonzero : n ≠ 0) (smooth : ContDiffAt ℝ n F (p, x))
    (D : E ≃L[ℝ] E) (spatial : HasFDerivAt (fun z => F (p, z)) D.toContinuousLinearMap x)
    (agreement : ∀ᶠ a in 𝓝 p, ∀ z, H a z = F (a, z)) :
    ContDiffAt ℝ n (fun q : P × E => (H q.1).symm q.2) (p, F (p, x)) := by
  let S : P × E → P × E := fun q => (q.1, F q)
  let G : P × E → P × E := fun q => (q.1, (H q.1).symm q.2)
  let B := fderiv ℝ (fun a => F (a, x)) p
  let L : (P × E) ≃L[ℝ] (P × E) := (ContinuousLinearEquiv.refl ℝ P).skewProd D B
  have derivative := ParametricInverseDerivative.hasFDerivAt_coprod_of_partials F p x D
    (smooth.differentiableAt nonzero) spatial
  have skewDerivative : HasFDerivAt S L.toContinuousLinearMap (p, x) := by
    convert (hasFDerivAt_fst (p := (p, x))).prodMk derivative using 1
    apply ContinuousLinearMap.ext
    intro v
    change (v.1, D v.2 + B v.1) = (v.1, B v.1 + D v.2)
    exact Prod.ext rfl (add_comm _ _)
  have skewSmooth : ContDiffAt ℝ n S (p, x) := contDiffAt_fst.prodMk smooth
  have left : ∀ᶠ q in 𝓝 (p, x), G (S q) = q := by
    have near := (continuous_fst.continuousAt (x := (p, x))).eventually agreement
    filter_upwards [near] with q hq
    exact Prod.ext rfl (by
      change (H q.1).symm (F (q.1, q.2)) = q.2
      rw [← hq q.2, Homeomorph.symm_apply_apply])
  have inverse := ContDiffLocalLeftInverse.contDiffAt_of_eventually_leftInverse
    skewSmooth skewDerivative nonzero left
  exact contDiffAt_snd.comp (S (p, x)) inverse

/-- In particular, the literal uniformly small affine-perturbation family
has a jointly regular inverse whenever its literal residual family does. -/
theorem contDiffAt_smallAffine_inverse (A : E ≃L[ℝ] E) (b : E) (u : P × E → E)
    (k : ℝ≥0) (lip : ∀ p, LipschitzWith k (fun x => u (p, x)))
    (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (du : ∀ p, Differentiable ℝ (fun x => u (p, x))) (p : P) (x : E)
    {n : ℕ∞ω} (nonzero : n ≠ 0) (smooth : ContDiffAt ℝ n u (p, x)) :
    ContDiffAt ℝ n
      (fun q : P × E => (SmallAffinePerturbation.homeomorph A b (lip q.1) small).symm q.2)
      (p, A x+b+u (p, x)) := by
  let F : P × E → E := fun q => A q.2+b+u q
  let H : P → E ≃ₜ E := fun a => SmallAffinePerturbation.homeomorph A b (lip a) small
  let D := SmallAffinePerturbation.derivativeEquiv A b (lip p) small (du p) x
  have forward : ContDiffAt ℝ n F (p, x) :=
    ((A.contDiff.contDiffAt.comp (p, x) contDiffAt_snd).add contDiffAt_const).add smooth
  have spatial : HasFDerivAt (fun z => F (p, z)) D.toContinuousLinearMap x := by
    rw [SmallAffinePerturbation.derivativeEquiv_coe]
    exact ((A.differentiable.add_const b).add (du p) x).hasFDerivAt
  exact contDiffAt_inverse_family F H p x nonzero forward D spatial
    (Eventually.of_forall (fun _ _ => rfl))

end LeanShared.ParametricGlobalInverseRegularity
