module

public import LeanShared.Geometry.UnitAddCircleManifold
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.NormNum

/-! The differential of the actual real quotient projection to the smooth
unit additive circle is invertible. Composing with its concrete smooth
complex embedding gives exp(2πit), whose ordinary real derivative never
vanishes. The chain rule gives injectivity, and both tangent dimensions
are one. No local-diffeomorphism or tangent-frame source is supplied. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.UnitAddCircleManifold

def projection (t : ℝ) : UnitAddCircle := t
def ambient (x : UnitAddCircle) : ℂ := equivalence x
def angularCoefficient : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
def ambientLift (t : ℝ) : ℂ := Complex.exp (angularCoefficient * (t : ℂ))
def derivativeCoefficient (t : ℝ) : ℂ := ambientLift t * angularCoefficient

theorem angularCoefficient_ne_zero : angularCoefficient ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) Complex.I_ne_zero

theorem derivativeCoefficient_ne_zero (t : ℝ) : derivativeCoefficient t ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) angularCoefficient_ne_zero

theorem ambient_projection (t : ℝ) : ambient (projection t) = ambientLift t := by
  simp [ambient, projection, equivalence_coe, Circle.coe_exp, ambientLift, angularCoefficient,
    mul_comm, mul_left_comm]

theorem hasDerivAt_ambientLift (t : ℝ) : HasDerivAt ambientLift (derivativeCoefficient t) t := by
  have linear : HasDerivAt (fun u : ℝ => angularCoefficient * (u : ℂ)) angularCoefficient t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      (hasDerivAt_id t).ofReal_comp.const_mul angularCoefficient
  simpa only [ambientLift, derivativeCoefficient] using! linear.cexp

theorem smooth_ambient : ContMDiff (𝓘(ℝ, Model)) (𝓘(ℝ, ℂ)) ∞ ambient := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  exact (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp smooth_equivalence

theorem projectionDifferential_injective (t : ℝ) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t) := by
  have chain : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (ambient ∘ projection) t =
      (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, ℂ)) ambient (projection t)).comp
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t) :=
    mfderiv_comp t ((smooth_ambient.mdifferentiable (by simp)) (projection t))
      ((smooth_projection.mdifferentiable (by simp)) t)
  intro v w same
  have ambientSame : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (ambient ∘ projection) t v =
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (ambient ∘ projection) t w := by
    rw [chain]
    exact congrArg (mfderiv (𝓘(ℝ, Model)) (𝓘(ℝ, ℂ)) ambient (projection t)) same
  have form : ambient ∘ projection = ambientLift := funext ambient_projection
  rw [form, mfderiv_eq_fderiv, (hasDerivAt_ambientLift t).hasFDerivAt.fderiv] at ambientSame
  change (v : ℝ) = (w : ℝ)
  apply Complex.ofReal_injective
  apply mul_right_cancel₀ (derivativeCoefficient_ne_zero t)
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul] using! ambientSame

theorem projectionDifferential_bijective (t : ℝ) :
    Function.Bijective (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t) := by
  have dimension : Module.finrank ℝ (TangentSpace (𝓘(ℝ, ℝ)) t) =
      Module.finrank ℝ (TangentSpace (𝓘(ℝ, Model)) (projection t)) := by
    rw [(NormedSpace.fromTangentSpace (𝕜 := ℝ) t).toLinearEquiv.finrank_eq,
      (tangentSpaceCastModel (𝓘(ℝ, Model)) (projection t)).toLinearEquiv.finrank_eq]
    simp [Model]
  exact ⟨projectionDifferential_injective t,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimension).mp
      (projectionDifferential_injective t)⟩

/-- The actual quotient differential, with its inverse constructed from
the proved finite-dimensional bijectivity. -/
def projectionDifferentialEquiv (t : ℝ) :
    TangentSpace (𝓘(ℝ, ℝ)) t ≃L[ℝ] TangentSpace (𝓘(ℝ, Model)) (projection t) :=
  (LinearEquiv.ofBijective (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t).toLinearMap
    (projectionDifferential_bijective t)).toContinuousLinearEquiv

theorem projectionDifferentialEquiv_apply (t : ℝ) (v : TangentSpace (𝓘(ℝ, ℝ)) t) :
    projectionDifferentialEquiv t v = mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t v := rfl

end LeanShared.UnitAddCircleManifold
