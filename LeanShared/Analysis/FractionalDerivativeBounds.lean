module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform fractional derivative bounds from actual perturbation controls

For `r=m+delta`, the data consist of actual derivatives through order `m`
and the `delta`-Hölder bound of the highest derivative. Thus noninteger
regularity is retained. Bounds on the derivative differences and their
highest-order increments produce uniform bounds for perturbed maps and
weights, as needed by parameter-bounded microlocal estimates.

This does not assume a uniform microlocal operator estimate. That classical
input must be parameterized by these bounds together with fixed cutoffs,
compact support, common cone separation and inverse/Jacobian bounds.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.FractionalDerivativeBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bound on the actual `C^{m+delta}` data on the coordinate compact. -/
structure Bounds (f : E → F) (K : Set E) (m : ℕ) (δ B : ℝ) : Prop where
  regularity : ContDiff ℝ m f
  derivatives : ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B
  highest : ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ B * ‖x - y‖ ^ δ

/-- Difference controls are on the actual derivative fields. Their top
increments are the fractional seminorm part of the perturbation distance. -/
structure Difference (f g : E → F) (K : Set E) (m : ℕ) (δ ε : ℝ) : Prop where
  derivatives : ∀ k ≤ m, ∀ x ∈ K,
    ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x‖ ≤ ε
  highest : ∀ x ∈ K, ∀ y ∈ K,
    ‖(iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y) -
      (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y)‖ ≤ ε * ‖x - y‖ ^ δ

theorem Bounds.of_difference {f g : E → F} {K : Set E} {m : ℕ} {δ B ε : ℝ}
    (hg : Bounds g K m δ B) (hf : ContDiff ℝ m f) (hd : Difference f g K m δ ε) :
    Bounds f K m δ (B + ε) := by
  refine ⟨hf, ?_, ?_⟩
  · intro k hk x hx
    exact (norm_le_norm_sub_add _ _).trans
      ((add_le_add (hd.derivatives k hk x hx) (hg.derivatives k hk x hx)).trans_eq (add_comm ε B))
  · intro x hx y hy
    calc
      _ ≤ ‖(iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y) -
          (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y)‖ +
          ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ := norm_le_norm_sub_add _ _
      _ ≤ ε * ‖x - y‖ ^ δ + B * ‖x - y‖ ^ δ :=
        add_le_add (hd.highest x hx y hy) (hg.highest x hx y hy)
      _ = (B + ε) * ‖x - y‖ ^ δ := by rw [← add_mul, add_comm ε B]

theorem Bounds.mono {f : E → F} {K : Set E} {m : ℕ} {δ B C : ℝ}
    (hf : Bounds f K m δ B) (hBC : B ≤ C) : Bounds f K m δ C :=
  ⟨hf.regularity, fun k hk x hx => (hf.derivatives k hk x hx).trans hBC,
    fun x hx y hy => (hf.highest x hx y hy).trans
      (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg (norm_nonneg _) _))⟩

/-- The usual `A*epsilon` perturbation controls give one uniform bound
for all noise parameters at intensities at most one. The map and weight
cases use the same actual fractional-derivative argument. -/
theorem uniform_noise_bounds {Ω : Type*} (family : Ω → E → F) (g : E → F)
    (K : Set E) (m : ℕ) (δ B A ε : ℝ) (hA : 0 ≤ A) (hε : ε ≤ 1)
    (hg : Bounds g K m δ B) (hfamily : ∀ ω, ContDiff ℝ m (family ω))
    (hdifference : ∀ ω, Difference (family ω) g K m δ (A * ε)) :
    ∀ ω, Bounds (family ω) K m δ (B + A) := by
  intro ω
  apply (hg.of_difference (hfamily ω) (hdifference ω)).mono
  exact add_le_add le_rfl (by simpa using mul_le_mul_of_nonneg_left hε hA)

end LeanShared.FractionalDerivativeBounds
