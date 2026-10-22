module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fixed Schwartz kernel bounds on compact source sets

Fixed kernels are globally Lipschitz and decay uniformly under translations
by points of a fixed compact set. These are actual Schwartz-function bounds,
not assumptions of a compactness theorem. Pairing the translated kernels and
their derivatives with bounded finite-order distributions is a later adapter.
-/

@[expose] public noncomputable section

open Set
open scoped SchwartzMap NNReal

namespace LeanShared.SchwartzKernelBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Polynomial-weighted bounds follow from the defining Schwartz seminorms. -/
theorem exists_polynomial_bound (ψ : 𝓢(E, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (1 + ‖x‖) ^ m * ‖ψ x‖ ≤ C := by
  let S : Seminorm ℂ 𝓢(E, ℂ) :=
    (Finset.Iic (m, 0)).sup (fun j => SchwartzMap.seminorm ℂ j.1 j.2)
  refine ⟨2 ^ m * S ψ, mul_nonneg (by positivity) (apply_nonneg S ψ), ?_⟩
  intro x
  simpa only [norm_iteratedFDeriv_zero] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, 0))
      (k := m) (n := 0) le_rfl le_rfl ψ x

/-- Translation over a compact set preserves a common polynomial decay bound. -/
theorem exists_uniform_translated_polynomial_bound (ψ : 𝓢(E, ℂ))
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : E, ∀ y ∈ K,
      (1 + ‖x‖) ^ m * ‖ψ (x - y)‖ ≤ A := by
  obtain ⟨R, hR, hyR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_bound ψ m
  refine ⟨(1 + R) ^ m * C, mul_nonneg (by positivity) hC, ?_⟩
  intro x y hy
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  have hbase : 1 + ‖x‖ ≤ (1 + R) * (1 + ‖x - y‖) := by
    have hn := norm_nonneg (x - y)
    have hyy := hyR y hy
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) hbase m
  calc
    (1 + ‖x‖) ^ m * ‖ψ (x - y)‖ ≤
        ((1 + R) * (1 + ‖x - y‖)) ^ m * ‖ψ (x - y)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (1 + R) ^ m * ((1 + ‖x - y‖) ^ m * ‖ψ (x - y)‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ (1 + R) ^ m * C :=
      mul_le_mul_of_nonneg_left (hbound (x - y)) (by positivity)

/-- The same translated bound expressed in the radial envelope used for leaves. -/
theorem exists_uniform_translated_decay (ψ : 𝓢(E, ℂ))
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : E, ∀ y ∈ K,
      ‖ψ (x - y)‖ ≤ A * (1 + ‖x‖) ^ (-(m : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_translated_polynomial_bound ψ hK m
  refine ⟨A, hA, ?_⟩
  intro x y hy
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hbound x y hy

/-- A fixed Schwartz kernel is globally Lipschitz, uniformly over translations. -/
theorem exists_lipschitz (ψ : 𝓢(E, ℂ)) : ∃ L : ℝ≥0, LipschitzWith L ψ := by
  let C := SchwartzMap.seminorm ℂ 0 1 ψ
  have hC : 0 ≤ C := apply_nonneg (SchwartzMap.seminorm ℂ 0 1) ψ
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_fderiv_le
    ((ψ.smooth 1).differentiable (by norm_num)) ?_⟩
  intro x
  change ‖fderiv ℝ ψ x‖ ≤ C
  simpa only [norm_iteratedFDeriv_one] using
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ 1 x

end LeanShared.SchwartzKernelBounds
