module

public import LeanShared.Geometry.DiffeomorphismIterates
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! A genuine periodic point turns the actual iterated manifold derivative
into a native-fiber endomorphism by isometric equality transport. This avoids
silently replacing a merely continuous Riemannian norm by chart norms. -/
public noncomputable section
namespace LeanShared.DiffeomorphismDifferential
open IsManifold Bundle
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

@[expose] def nativeTransport (x y : M) (same : x = y) :
    TangentSpace (𝓘(ℝ,E)) x ≃ₗᵢ[ℝ] TangentSpace (𝓘(ℝ,E)) y := by
  subst y
  exact LinearIsometryEquiv.refl ℝ _

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem nativeTransport_apply (x y : M) (same : x = y) (v : TangentSpace (𝓘(ℝ,E)) x) :
    nativeTransport x y same v = v := by
  subst y
  rfl

@[expose] def periodicReturn (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (fixed : (T : M → M)^[p] x = x) :
    TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) x :=
  (differential (T ^ p) (DiffeomorphismIterates.mdifferentiable_pow T forward p)
    (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse p) x).trans
    (nativeTransport ((T ^ p) x) x
      (by simpa only [DiffeomorphismIterates.coe_pow] using fixed)).toContinuousLinearEquiv

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem periodicReturn_apply (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (fixed : (T : M → M)^[p] x = x) (v : TangentSpace (𝓘(ℝ,E)) x) :
    periodicReturn T forward inverse p x fixed v =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v := by
  have fixedPow : (T ^ p) x = x := by simpa only [DiffeomorphismIterates.coe_pow] using fixed
  change nativeTransport ((T ^ p) x) x fixedPow
    (differential (T ^ p) (DiffeomorphismIterates.mdifferentiable_pow T forward p)
      (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse p) x v) = _
  rw [nativeTransport_apply]
  have actual := differential_apply (T ^ p) (DiffeomorphismIterates.mdifferentiable_pow T forward p)
    (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse p) x v
  have same := congrArg (fun L : E →L[ℝ] E => L v)
    (mfderiv_congr (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (x := x) (DiffeomorphismIterates.coe_pow T p))
  exact actual.trans same

end LeanShared.DiffeomorphismDifferential
