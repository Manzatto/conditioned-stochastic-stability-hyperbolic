module

public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import LeanShared.Analysis.InvariantDerivativeCocycle
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Derivatives of the literal chronological random word

Actual derivatives at actual prefix states construct the full derivative
word. The chain rule identifies this constructed word with `fderiv` of the
successive random maps. No derivative cocycle is supplied independently.
-/

@[expose] public noncomputable section

namespace LeanShared.FiniteDerivativeWord

open CylinderPrincipalCoefficient
open scoped Topology

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A literal local differentiable inverse gives injectivity of the actual
spatial derivative; no nonzero determinant is supplied. -/
theorem fderiv_injective_of_local_inverse (F B : E → E) (x : E)
    (hF : DifferentiableAt ℝ F x) (hB : DifferentiableAt ℝ B (F x))
    (hleft : ∀ᶠ y in 𝓝 x, B (F y) = y) : Function.Injective (fderiv ℝ F x) := by
  have hc := hB.hasFDerivAt.comp x hF.hasFDerivAt
  have hid : HasFDerivAt (B ∘ F) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hleft
  have he := hc.unique hid
  have heapply (v : E) : fderiv ℝ B (F x) (fderiv ℝ F x v) = v := by
    change ((fderiv ℝ B (F x)).comp (fderiv ℝ F x)) v = v
    rw [he]
    rfl
  intro u v huv
  exact (heapply u).symm.trans ((congrArg (fderiv ℝ B (F x)) huv).trans (heapply v))

def prefixDerivative (F : G → E → E) {N : ℕ} (word : Fin N → G) (x : E) : ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | k + 1 => if h : k < N then
      (fderiv ℝ (F (word ⟨k, h⟩)) (prefixOrbit F word k x)).comp (prefixDerivative F word x k)
    else prefixDerivative F word x k

theorem hasFDerivAt_prefixOrbit (F : G → E → E) (hF : ∀ a, Differentiable ℝ (F a))
    {N : ℕ} (word : Fin N → G) (k : ℕ) (x : E) :
    HasFDerivAt (prefixOrbit F word k) (prefixDerivative F word x k) x := by
  induction k with
  | zero => exact hasFDerivAt_id x
  | succ k ih =>
    by_cases hk : k < N
    · simpa only [prefixOrbit, prefixDerivative, dite_eq_left hk, Function.comp_def] using
        (hF (word ⟨k, hk⟩) (prefixOrbit F word k x)).hasFDerivAt.comp x ih
    · simpa only [prefixOrbit, prefixDerivative, dite_eq_right hk] using ih

theorem fderiv_prefixOrbit (F : G → E → E) (hF : ∀ a, Differentiable ℝ (F a))
    {N : ℕ} (word : Fin N → G) (k : ℕ) (x : E) :
    fderiv ℝ (prefixOrbit F word k) x = prefixDerivative F word x k :=
  (hasFDerivAt_prefixOrbit F hF word k x).fderiv

def jacobianProduct [FiniteDimensional ℝ E] (F : G → E → E) {N : ℕ}
    (word : Fin N → G) (x : E) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if h : k < N then
      |(fderiv ℝ (F (word ⟨k, h⟩)) (prefixOrbit F word k x)).det| * jacobianProduct F word x k
    else jacobianProduct F word x k

variable [FiniteDimensional ℝ E]

theorem abs_det_prefixDerivative (F : G → E → E) {N : ℕ}
    (word : Fin N → G) (k : ℕ) (x : E) :
    |(prefixDerivative F word x k).det| = jacobianProduct F word x k := by
  induction k with
  | zero => simp [prefixDerivative, jacobianProduct, ContinuousLinearMap.det]
  | succ k ih =>
    by_cases hk : k < N
    · simp only [prefixDerivative, jacobianProduct, dite_eq_left hk]
      change |LinearMap.det ((fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)).toLinearMap.comp
        (prefixDerivative F word x k).toLinearMap)| = _
      rw [LinearMap.det_comp, abs_mul, ih]
    · simpa only [prefixDerivative, jacobianProduct, dite_eq_right hk] using ih

theorem abs_det_fderiv_prefixOrbit (F : G → E → E) (hF : ∀ a, Differentiable ℝ (F a))
    {N : ℕ} (word : Fin N → G) (k : ℕ) (x : E) :
    |(fderiv ℝ (prefixOrbit F word k) x).det| = jacobianProduct F word x k := by
  rw [fderiv_prefixOrbit F hF, abs_det_prefixDerivative]

end LeanShared.FiniteDerivativeWord
