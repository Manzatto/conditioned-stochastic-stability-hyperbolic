module
public import LeanShared.Dynamics.HyperbolicAdaptedFrameBlocks
public import LeanShared.Geometry.CompactRiemannianMFDeriv
public import LeanShared.Geometry.DiffeomorphismInverseDifferential
import Mathlib.Tactic.Linarith

/-! The actual diagonal one-step affine prototypes have common forward
and inverse operator bounds in the already chosen adapted whole frames. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem PatchSystem.prototype_bounds (system : PatchSystem b)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M)) :
    ∃ B > 0, ∀ c d x : Λ, ∀ hx : x ∈ system.frameDomain c,
      ∀ ht : forwardPoint b x ∈ system.frameDomain d,
      let e := system.referenceFrame c ⟨x, hx⟩
      let f := system.referenceFrame d ⟨forwardPoint b x, ht⟩
      ∀ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.stableDimension),
      ∀ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.unstableDimension),
      f.symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val).comp e.toContinuousLinearMap) =
          U.toContinuousLinearMap.prodMap S.toContinuousLinearMap →
      ‖(U.prodCongr S).toContinuousLinearMap‖ ≤ B ∧
        ‖(U.prodCongr S).symm.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨C, positiveC, boundC⟩ := CompactRiemannianMFDeriv.exists_norm_bound T forward Λ b.hyperbolic.compact
  obtain ⟨D, positiveD, boundD⟩ := CompactRiemannianMFDeriv.exists_norm_bound T.symm backward Λ b.hyperbolic.compact
  let B := system.inverse_bound * ((C + D) * 2) + 1
  have positiveB : 0 < B := by
    have positiveI := system.inverse_bound_pos
    dsimp only [B]
    positivity
  refine ⟨B, positiveB, ?_⟩
  intro c d x hx ht
  dsimp only
  intro S U action
  let e := system.referenceFrame c ⟨x, hx⟩
  let f := system.referenceFrame d ⟨forwardPoint b x, ht⟩
  have target : T x.val ∈ Λ := (forwardPoint b x).property
  have boundsE := system.whole_bounds c ⟨x.val, x.property, hx.1⟩
  have boundsF := system.whole_bounds d ⟨T x.val, target, ht.1⟩
  have forwardE : ‖e.toContinuousLinearMap‖ ≤ 2 := boundsE.1
  have inverseE : ‖e.symm.toContinuousLinearMap‖ ≤ system.inverse_bound := boundsE.2
  have forwardF : ‖f.toContinuousLinearMap‖ ≤ 2 := boundsF.1
  have inverseF : ‖f.symm.toContinuousLinearMap‖ ≤ system.inverse_bound := boundsF.2
  let A := DiffeomorphismDifferential.differential T
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) x.val
  have normA : ‖A.toContinuousLinearMap‖ ≤ C := by
    convert boundC x.val x.property using 1
    congr 1
  have normInvA : ‖A.symm.toContinuousLinearMap‖ ≤ D := by
    apply ContinuousLinearMap.opNorm_le_bound _ positiveD.le
    intro v
    have estimate := ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm (T x.val)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (boundD (T x.val) target) (norm_nonneg _))
    rw [← DiffeomorphismDifferential.differential_symm_apply T
      (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) x.val v] at estimate
    have normEq := congrArg (fun y : M => @norm (TangentSpace (𝓘(ℝ, E)) y)
      (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y).toNorm
        (A.symm v)) (T.symm_apply_apply x.val)
    exact normEq.ge.trans estimate
  have coordinate : (e.trans A).trans f.symm = U.prodCongr S := by
    apply ContinuousLinearEquiv.ext
    funext v
    have formula := congrArg (fun F => F v) action
    change f.symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val (e v)) = (U v.1, S v.2) at formula
    change f.symm (A (e v)) = (U v.1, S v.2)
    rw [DiffeomorphismDifferential.differential_apply]
    exact formula
  have forwardFormula : (U.prodCongr S).toContinuousLinearMap =
      f.symm.toContinuousLinearMap.comp (A.toContinuousLinearMap.comp e.toContinuousLinearMap) := by
    rw [← coordinate]
    rfl
  have inverseFormula : (U.prodCongr S).symm.toContinuousLinearMap =
      e.symm.toContinuousLinearMap.comp (A.symm.toContinuousLinearMap.comp f.toContinuousLinearMap) := by
    rw [← coordinate]
    rfl
  constructor
  · rw [forwardFormula]
    calc
      _ ≤ ‖f.symm.toContinuousLinearMap‖ * (‖A.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ system.inverse_bound * (C * 2) := mul_le_mul inverseF
        (mul_le_mul normA forwardE (norm_nonneg e.toContinuousLinearMap) positiveC.le)
        (mul_nonneg (norm_nonneg A.toContinuousLinearMap) (norm_nonneg e.toContinuousLinearMap)) system.inverse_bound_pos.le
      _ ≤ B := by dsimp only [B]; nlinarith [mul_pos system.inverse_bound_pos positiveD]
  · rw [inverseFormula]
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖A.symm.toContinuousLinearMap‖ * ‖f.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ system.inverse_bound * (D * 2) := mul_le_mul inverseE
        (mul_le_mul normInvA forwardF (norm_nonneg f.toContinuousLinearMap) positiveD.le)
        (mul_nonneg (norm_nonneg A.symm.toContinuousLinearMap) (norm_nonneg f.toContinuousLinearMap)) system.inverse_bound_pos.le
      _ ≤ B := by dsimp only [B]; nlinarith [mul_pos system.inverse_bound_pos positiveC]

end LeanShared.HyperbolicAdaptedPatchSystem
