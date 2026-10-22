module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Actual derivatives on invariant moving tangent fibers

The cocycle is the restriction of the literal derivative to an invariant
submodule field. Isometric frames identify the moving fibers with one fixed
finite-dimensional model. They do not supply a cocycle or Jacobian as data:
both are constructed from `fderiv`. The chain rule proves composition and
absolute Jacobian multiplicativity, while operator norms give the genuine
hyperbolicity submultiplicativity. A manifold application still needs its
coordinate tangent/volume identification and classical bundle construction.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.InvariantDerivativeCocycle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Restriction between distinct tangent fibers. For a random word these
are the transported fibers at consecutive times, not a common bundle
assumed invariant under all nearby maps. -/
def framedRestriction (A : E →L[ℝ] E) (U V : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (hA : MapsTo A U V) : H →L[ℝ] H :=
  (eV.symm : V →L[ℝ] H).comp ((A.restrict hA).comp (eU : H →L[ℝ] U))

theorem framedRestriction_intertwines (A : E →L[ℝ] E) (U V : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (hA : MapsTo A U V) (v : H) :
    (eV (framedRestriction A U V eU eV hA v) : E) = A (eU v) := by
  simp [framedRestriction]
  rfl

theorem framedRestriction_comp (A B : E →L[ℝ] E) (U V W : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (eW : H ≃ₗᵢ[ℝ] W)
    (hA : MapsTo A U V) (hB : MapsTo B V W) :
    framedRestriction (B.comp A) U W eU eW (fun _ hx => hB (hA hx)) =
      (framedRestriction B V W eV eW hB).comp (framedRestriction A U V eU eV hA) := by
  ext v
  simp [framedRestriction]
  rfl

theorem norm_framedRestriction (A : E →L[ℝ] E) (U V : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (hA : MapsTo A U V) :
    ‖framedRestriction A U V eU eV hA‖ = ‖A.restrict hA‖ := by
  unfold framedRestriction
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- Actual chain rule with three possibly different fibers. -/
theorem framed_fderiv_comp (F G : E → E) (x : E) (U V W : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (eW : H ≃ₗᵢ[ℝ] W)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x))
    (hA : MapsTo (fderiv ℝ F x) U V) (hB : MapsTo (fderiv ℝ G (F x)) V W)
    (hGF : MapsTo (fderiv ℝ (G ∘ F) x) U W) :
    framedRestriction (fderiv ℝ (G ∘ F) x) U W eU eW hGF =
      (framedRestriction (fderiv ℝ G (F x)) V W eV eW hB).comp
        (framedRestriction (fderiv ℝ F x) U V eU eV hA) := by
  ext v
  apply eW.injective
  apply Subtype.ext
  rw [framedRestriction_intertwines (fderiv ℝ (G ∘ F) x) U W eU eW hGF v]
  change fderiv ℝ (G ∘ F) x (eU v) =
    (eW (framedRestriction (fderiv ℝ G (F x)) V W eV eW hB
      (framedRestriction (fderiv ℝ F x) U V eU eV hA v)) : E)
  rw [framedRestriction_intertwines, framedRestriction_intertwines,
    fderiv_comp x hG hF]
  rfl

def frameDerivative (F : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x))) (x : E) : H →L[ℝ] H :=
  (e (F x)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((fderiv ℝ F x).restrict (hInv x)).comp
      (e x).toContinuousLinearEquiv.toContinuousLinearMap)

theorem frameDerivative_intertwines (F : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x))) (x : E) (v : H) :
    ((e (F x)) (frameDerivative F U e hInv x v) : E) =
      fderiv ℝ F x (e x v) := by
  simp [frameDerivative]
  rfl

theorem invariant_comp (F G : E → E) (U : E → Submodule ℝ E)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hGInv : ∀ x, MapsTo (fderiv ℝ G x) (U x) (U (G x))) :
    ∀ x, MapsTo (fderiv ℝ (G ∘ F) x) (U x) (U ((G ∘ F) x)) := by
  intro x v hv
  rw [fderiv_comp x (hG (F x)) (hF x)]
  exact hGInv (F x) (hFInv x hv)

theorem frameDerivative_comp (F G : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hGInv : ∀ x, MapsTo (fderiv ℝ G x) (U x) (U (G x))) (x : E) :
    frameDerivative (G ∘ F) U e (invariant_comp F G U hF hG hFInv hGInv) x =
      (frameDerivative G U e hGInv (F x)).comp (frameDerivative F U e hFInv x) := by
  ext v
  apply (e (G (F x))).injective
  apply Subtype.ext
  change ((e ((G ∘ F) x))
    (frameDerivative (G ∘ F) U e (invariant_comp F G U hF hG hFInv hGInv) x v) : E) =
    ((e (G (F x))) (frameDerivative G U e hGInv (F x)
      (frameDerivative F U e hFInv x v)) : E)
  rw [frameDerivative_intertwines (G ∘ F) U e _ x v,
    frameDerivative_intertwines G U e hGInv (F x),
    fderiv_comp x (hG (F x)) (hF x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← frameDerivative_intertwines F U e hFInv x v]

/-- The framed norm is the intrinsic norm of the derivative between the
actual submodule fibers, because both frames are isometries. -/
theorem norm_frameDerivative (F : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x))) (x : E) :
    ‖frameDerivative F U e hInv x‖ = ‖(fderiv ℝ F x).restrict (hInv x)‖ := by
  unfold frameDerivative
  change ‖((e (F x)).symm : U (F x) →L[ℝ] H).comp
    (((fderiv ℝ F x).restrict (hInv x)).comp (e x : H →L[ℝ] U x))‖ = _
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem norm_frameDerivative_comp_le (F G : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hGInv : ∀ x, MapsTo (fderiv ℝ G x) (U x) (U (G x))) (x : E) :
    ‖frameDerivative (G ∘ F) U e (invariant_comp F G U hF hG hFInv hGInv) x‖ ≤
      ‖frameDerivative G U e hGInv (F x)‖ * ‖frameDerivative F U e hFInv x‖ := by
  rw [frameDerivative_comp F G U e hF hG hFInv hGInv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem frameDerivative_id (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ (id : E → E) x) (U x) (U (id x))) (x : E) :
    frameDerivative id U e hInv x = ContinuousLinearMap.id ℝ H := by
  ext v
  apply (e x).injective
  apply Subtype.ext
  have h := frameDerivative_intertwines id U e hInv x v
  simpa using h

theorem frameDerivative_inverse_comp (F B : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hB : Differentiable ℝ B)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hBInv : ∀ x, MapsTo (fderiv ℝ B x) (U x) (U (B x)))
    (hleft : ∀ x, B (F x) = x) (x : E) :
    (frameDerivative B U e hBInv (F x)).comp (frameDerivative F U e hFInv x) =
      ContinuousLinearMap.id ℝ H := by
  rw [← frameDerivative_comp F B U e hF hB hFInv hBInv]
  have hBF : B ∘ F = id := funext hleft
  simp only [hBF, frameDerivative_id]

def unstableJacobian [FiniteDimensional ℝ H] (F : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x))) (x : E) : ℝ :=
  |(frameDerivative F U e hInv x).det|

variable [FiniteDimensional ℝ H]

theorem unstableJacobian_comp (F G : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hGInv : ∀ x, MapsTo (fderiv ℝ G x) (U x) (U (G x))) (x : E) :
    unstableJacobian (G ∘ F) U e (invariant_comp F G U hF hG hFInv hGInv) x =
      unstableJacobian G U e hGInv (F x) * unstableJacobian F U e hFInv x := by
  unfold unstableJacobian
  rw [frameDerivative_comp F G U e hF hG hFInv hGInv]
  change |LinearMap.det ((frameDerivative G U e hGInv (F x)).toLinearMap.comp
    (frameDerivative F U e hFInv x).toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul]

theorem unstableJacobian_inverse_mul (F B : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hB : Differentiable ℝ B)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hBInv : ∀ x, MapsTo (fderiv ℝ B x) (U x) (U (B x)))
    (hleft : ∀ x, B (F x) = x) (x : E) :
    unstableJacobian B U e hBInv (F x) * unstableJacobian F U e hFInv x = 1 := by
  have he := congrArg (fun A : H →L[ℝ] H => |A.det|)
    (frameDerivative_inverse_comp F B U e hF hB hFInv hBInv hleft x)
  change |LinearMap.det ((frameDerivative B U e hBInv (F x)).toLinearMap.comp
    (frameDerivative F U e hFInv x).toLinearMap)| = |LinearMap.det LinearMap.id| at he
  simpa only [unstableJacobian, LinearMap.det_comp, LinearMap.det_id, abs_mul, abs_one] using he

theorem unstableJacobian_pos_of_inverse (F B : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hF : Differentiable ℝ F) (hB : Differentiable ℝ B)
    (hFInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x)))
    (hBInv : ∀ x, MapsTo (fderiv ℝ B x) (U x) (U (B x)))
    (hleft : ∀ x, B (F x) = x) (x : E) : 0 < unstableJacobian F U e hFInv x := by
  have hprod := unstableJacobian_inverse_mul F B U e hF hB hFInv hBInv hleft x
  have hne : unstableJacobian F U e hFInv x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact zero_ne_one hprod
  exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)

end LeanShared.InvariantDerivativeCocycle
