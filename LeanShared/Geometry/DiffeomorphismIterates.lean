module
public import LeanShared.Geometry.DiffeomorphismDifferential
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Actual iterates of a differentiable homeomorphism and its inverse have the
expected ordinary maps and differentiability. These identities permit genuine
hyperbolic tangent block equivalences without a separate cocycle certificate. -/
public noncomputable section
namespace LeanShared.DiffeomorphismIterates
open IsManifold
open scoped Manifold

theorem coe_pow {M : Type*} [TopologicalSpace M] (T : M ≃ₜ M) (n : ℕ) :
    ((T^n : M ≃ₜ M) : M → M) = (T : M → M)^[n] := by
  funext x
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [pow_succ, Homeomorph.mul_apply, Function.iterate_succ_apply, ih]

theorem coe_symm_pow {M : Type*} [TopologicalSpace M] (T : M ≃ₜ M) (n : ℕ) :
    ((T^n).symm : M → M) = (T.symm : M → M)^[n] := by
  have inverse : (T^n).symm = T.symm^n := by
    change (T^n)⁻¹ = (T⁻¹)^n
    exact (inv_pow T n).symm
  rw [inverse, coe_pow]

theorem mdifferentiable_iterate {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (f : M → M) (smooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) f) (n : ℕ) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[n]) := by
  induction n with
  | zero => exact mdifferentiable_id
  | succ n ih => rw [Function.iterate_succ']; exact smooth.comp ih

theorem mdifferentiable_pow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (T : M ≃ₜ M) (smooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T) (n : ℕ) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n : M ≃ₜ M) : M → M) := by
  rw [coe_pow]
  exact mdifferentiable_iterate T smooth n

theorem mdifferentiable_symm_pow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (T : M ≃ₜ M) (smooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) (n : ℕ) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n).symm : M → M) := by
  rw [coe_symm_pow]
  exact mdifferentiable_iterate T.symm smooth n

end LeanShared.DiffeomorphismIterates
