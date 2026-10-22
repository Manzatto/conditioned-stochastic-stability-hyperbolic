module

public import LeanShared.Analysis.WordHyperbolicityFactors
public import LeanShared.Analysis.InverseJacobianWeight
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-!
# Continuous Jacobian factors of actual smooth map families

The intrinsic norm determinant is expressed by the Gram matrix of actual
derivative images, so its continuity is proved directly. Joint `C¹`
regularity of the nonlinear family then gives continuity of the full-word
derivative. A continuous local orthonormal frame for the initial unstable
bundle produces the continuous actual unstable Jacobian factor.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.ContinuousTangentJacobian

open CylinderPrincipalCoefficient FiniteDerivativeWord

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem normDet_eq_sqrt_gram (A : H →L[ℝ] E) :
    A.toLinearMap.normDet = Real.sqrt
      (Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ H i))).det := by
  have hsq : A.toLinearMap.normDet ^ 2 =
      (Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ H i))).det := by
    simpa using A.toLinearMap.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ H)
  rw [← hsq, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

theorem continuous_normDet : Continuous (fun A : H →L[ℝ] E => A.toLinearMap.normDet) := by
  have hg : Continuous (fun A : H →L[ℝ] E =>
      Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ H i))) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.gram_apply]
    fun_prop
  have hformula : (fun A : H →L[ℝ] E => A.toLinearMap.normDet) =
      (fun A => Real.sqrt (Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ H i))).det) :=
    funext normDet_eq_sqrt_gram
  rw [hformula]
  exact Real.continuous_sqrt.comp hg.matrix_det

section IntrinsicFrame

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The frame formula is the intrinsic Jacobian on its actual tangent
range; frames do not alter the coefficient. -/
theorem normDet_comp_frame (A : E →L[ℝ] E) (e : H →ₗᵢ[ℝ] E) :
    (A.comp e.toContinuousLinearMap).toLinearMap.normDet =
      (A.domRestrict e.toLinearMap.range).toLinearMap.normDet := by
  change ((A.domRestrict e.toLinearMap.range).toLinearMap.comp
    e.equivRange.toLinearEquiv.toLinearMap).normDet = _
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ e.equivRange.toLinearEquiv.finrank_eq]
  have he : e.equivRange.toLinearEquiv.toLinearMap.normDet = 1 :=
    e.equivRange.toLinearIsometry.normDet_eq_one
  rw [he, mul_one]

theorem unstableJacobian_eq_frame {G : Type*} (F : G → E → E) {N : ℕ}
    (word : Fin N → G) (x : E) (e : H →ₗᵢ[ℝ] E) (k : ℕ) :
    WordHyperbolicityFactors.unstableJacobian F word x e.toLinearMap.range k =
      ((prefixDerivative F word x k).comp e.toContinuousLinearMap).toLinearMap.normDet := by
  rw [normDet_comp_frame]
  unfold WordHyperbolicityFactors.unstableJacobian
  change (((prefixDerivative F word x k).domRestrict e.toLinearMap.range).toLinearMap.codRestrict
    (DerivativeTransportFrames.transportedFiber F word x e.toLinearMap.range k) _).normDet = _
  exact LinearMap.normDet_codRestrict _

end IntrinsicFrame

section Word

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem continuous_prefixDerivative (F : E × P → E) (hF : ContDiff ℝ 1 F) (N k : ℕ) :
    Continuous (fun z : (Fin N → P) × E =>
      prefixDerivative (fun a x => F (x, a)) z.1 z.2 k) := by
  have hmaps : Continuous (fun z : P × E => F (z.2, z.1)) :=
    hF.continuous.comp continuous_swap
  have hD := InverseJacobianWeight.continuous_spatialDerivative_of_contDiff F hF
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    by_cases hk : k < N
    · have hd : Continuous (fun z : (Fin N → P) × E =>
          fderiv ℝ (fun x => F (x, z.1 ⟨k, hk⟩))
            (prefixOrbit (fun a x => F (x, a)) z.1 k z.2)) :=
        by
          simpa only [InverseJacobianWeight.spatialDerivative, Function.comp_def] using
            hD.comp ((continuous_prefixOrbit (fun a x => F (x, a)) hmaps N k).prodMk
              ((continuous_apply (⟨k, hk⟩ : Fin N)).comp continuous_fst))
      simpa only [prefixDerivative, dite_eq_left hk] using hd.clm_comp ih
    · simpa only [prefixDerivative, dite_eq_right hk] using ih

def framedUnstableJacobian (F : E × P → E) (frame : E → H →ₗᵢ[ℝ] E) (N : ℕ) :
    (Fin N → P) × E → ℝ := fun z =>
  ((prefixDerivative (fun a x => F (x, a)) z.1 z.2 N).comp
    (frame z.2).toContinuousLinearMap).toLinearMap.normDet

theorem continuous_framedUnstableJacobian (F : E × P → E) (hF : ContDiff ℝ 1 F)
    (frame : E → H →ₗᵢ[ℝ] E)
    (hframe : Continuous (fun x => (frame x).toContinuousLinearMap)) (N : ℕ) :
    Continuous (framedUnstableJacobian F frame N) :=
  continuous_normDet.comp ((continuous_prefixDerivative F hF N N).clm_comp
    (hframe.comp continuous_snd))

/-- End-to-end continuity of the exact intrinsic unstable word Jacobian,
from the nonlinear family's `C¹` regularity and a continuous geometric
orthonormal frame. There is no supplied continuous scalar Jacobian field. -/
theorem continuous_wordUnstableJacobian [FiniteDimensional ℝ E]
    (F : E × P → E) (hF : ContDiff ℝ 1 F) (frame : E → H →ₗᵢ[ℝ] E)
    (hframe : Continuous (fun x => (frame x).toContinuousLinearMap)) (N : ℕ) :
    Continuous (fun z : (Fin N → P) × E =>
      WordHyperbolicityFactors.unstableJacobian (fun a x => F (x, a)) z.1 z.2
        (frame z.2).toLinearMap.range N) := by
  have heq : (fun z : (Fin N → P) × E =>
      WordHyperbolicityFactors.unstableJacobian (fun a x => F (x, a)) z.1 z.2
        (frame z.2).toLinearMap.range N) = framedUnstableJacobian F frame N := by
    funext z
    exact unstableJacobian_eq_frame (fun a x => F (x, a)) z.1 z.2 (frame z.2) N
  rw [heq]
  exact continuous_framedUnstableJacobian F hF frame hframe N

end Word

end LeanShared.ContinuousTangentJacobian
