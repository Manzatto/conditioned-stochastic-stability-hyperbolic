module
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Completeness

/-! Derivatives of actual local right inverses converge by continuity of
inversion in the Banach algebra of operators. This requires convergence, not
a Lipschitz rate in a perturbation parameter. -/
public noncomputable section
namespace LeanShared.InverseDerivativeConvergence
open Filter
open scoped Topology

theorem rightInverse_tendsto
    {R A : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (a b : A → R) (l : Filter A) (u : Rˣ)
    (limit : Tendsto a l (𝓝 (u : R))) (right : ∀ᶠ i in l, a i * b i = 1) :
    Tendsto b l (𝓝 ((u⁻¹ : Rˣ) : R)) := by
  have units : ∀ᶠ i in l, IsUnit (a i) := limit.eventually (Units.isOpen.mem_nhds u.isUnit)
  have result := (NormedRing.inverse_continuousAt u).tendsto.comp limit
  rw [Ring.inverse_unit] at result
  apply result.congr'
  filter_upwards [units,right] with i hi hr
  calc
    Ring.inverse (a i) = Ring.inverse (a i) * (a i * b i) := by rw [hr,mul_one]
    _ = b i := Ring.inverse_mul_cancel_left _ _ hi

 theorem fderiv_tendsto
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : A → E → E) (v : A → E) (l : Filter A) (L : E ≃L[ℝ] E)
    (limit : Tendsto (fun i => fderiv ℝ (f i) (g i (v i))) l (𝓝 L.toContinuousLinearMap))
    (forward : ∀ᶠ i in l, DifferentiableAt ℝ (f i) (g i (v i)))
    (inverse : ∀ᶠ i in l, DifferentiableAt ℝ (g i) (v i))
    (identity : ∀ᶠ i in l, (f i ∘ g i) =ᶠ[𝓝 (v i)] id) :
    Tendsto (fun i => fderiv ℝ (g i) (v i)) l (𝓝 L.symm.toContinuousLinearMap) := by
  have right : ∀ᶠ i in l,
      fderiv ℝ (f i) (g i (v i)) * fderiv ℝ (g i) (v i) = 1 := by
    filter_upwards [forward,inverse,identity] with i hf hg hi
    have derivative := hi.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp (v i) hf hg,fderiv_id] at derivative
    exact derivative
  exact rightInverse_tendsto (R := E →L[ℝ] E)
    (fun i => fderiv ℝ (f i) (g i (v i))) (fun i => fderiv ℝ (g i) (v i)) l L.toUnit limit right

end LeanShared.InverseDerivativeConvergence
