module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Normalizing actual two-norm operator estimates

Dividing the operators by a positive `b` changes all growth rates by `1/b`.
Dividing the weak inclusion by `max 1 ‖ι‖` makes its norm at most one while
preserving injectivity and compactness. The estimates below are consequences
of actual scalar powers and the original bounds, not normalized inputs.
-/

@[expose] public noncomputable section

namespace LeanShared.TwoNormNormalization

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A positive normalization constant even for the zero inclusion. -/
def weakScale (ι : E →L[𝕜] F) : ℝ := max 1 ‖ι‖

theorem weakScale_one_le (ι : E →L[𝕜] F) : 1 ≤ weakScale ι := le_max_left _ _

theorem weakScale_pos (ι : E →L[𝕜] F) : 0 < weakScale ι :=
  zero_lt_one.trans_le (weakScale_one_le ι)

/-- The actual rescaled weak inclusion. -/
def weakEmbedding (ι : E →L[𝕜] F) : E →L[𝕜] F :=
  (((weakScale ι)⁻¹ : ℝ) : 𝕜) • ι

/-- The actual operator divided by a real positive reference rate. -/
def normalizedOperator (P : E →L[𝕜] E) (b : ℝ) : E →L[𝕜] E :=
  ((b⁻¹ : ℝ) : 𝕜) • P

theorem norm_weakEmbedding_apply (ι : E →L[𝕜] F) (x : E) :
    ‖weakEmbedding ι x‖ = ‖ι x‖ / weakScale ι := by
  rw [weakEmbedding, smul_apply, norm_smul,
    RCLike.norm_of_nonneg (inv_nonneg.mpr (weakScale_pos ι).le)]
  exact mul_comm _ _

theorem weakEmbedding_norm_le (ι : E →L[𝕜] F) (x : E) : ‖weakEmbedding ι x‖ ≤ ‖x‖ := by
  rw [norm_weakEmbedding_apply, div_le_iff₀ (weakScale_pos ι)]
  calc
    ‖ι x‖ ≤ ‖ι‖ * ‖x‖ := ι.le_opNorm x
    _ ≤ weakScale ι * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    _ = ‖x‖ * weakScale ι := mul_comm _ _

theorem norm_weakEmbedding_le_one (ι : E →L[𝕜] F) : ‖weakEmbedding ι‖ ≤ 1 := by
  apply (weakEmbedding ι).opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using weakEmbedding_norm_le ι x

theorem weakEmbedding_injective (ι : E →L[𝕜] F) (hi : Function.Injective ι) :
    Function.Injective (weakEmbedding ι) := by
  intro x y hxy
  apply hi
  apply smul_right_injective F (show (((weakScale ι)⁻¹ : ℝ) : 𝕜) ≠ 0 by
    exact_mod_cast inv_ne_zero (weakScale_pos ι).ne')
  exact hxy

theorem weakEmbedding_isCompact (ι : E →L[𝕜] F) (hi : IsCompactOperator ι) :
    IsCompactOperator (weakEmbedding ι) := by
  change IsCompactOperator (fun x => (((weakScale ι)⁻¹ : ℝ) : 𝕜) • ι x)
  exact hi.smul _

/-- The scalar-power identity holds over both real and complex spaces. -/
theorem normalizedOperator_pow (P : E →L[𝕜] E) (b : ℝ) (n : ℕ) :
    normalizedOperator P b ^ n = (((b⁻¹ : ℝ) : 𝕜) ^ n) • P ^ n :=
  smul_pow _ _ _

theorem norm_normalizedOperator_pow_apply (P : E →L[𝕜] E) (b : ℝ) (hb : 0 < b)
    (n : ℕ) (x : E) :
    ‖(normalizedOperator P b ^ n) x‖ = ‖(P ^ n) x‖ / b ^ n := by
  rw [normalizedOperator_pow, smul_apply, norm_smul, norm_pow,
    RCLike.norm_of_nonneg (inv_nonneg.mpr hb.le), inv_pow]
  exact mul_comm _ _

theorem norm_weak_normalizedOperator_pow_apply (P : E →L[𝕜] E) (ι : E →L[𝕜] F)
    (b : ℝ) (hb : 0 < b) (n : ℕ) (x : E) :
    ‖weakEmbedding ι ((normalizedOperator P b ^ n) x)‖ =
      ‖ι ((P ^ n) x)‖ / (weakScale ι * b ^ n) := by
  rw [norm_weakEmbedding_apply, normalizedOperator_pow, smul_apply,
    map_smul, norm_smul, norm_pow, RCLike.norm_of_nonneg (inv_nonneg.mpr hb.le), inv_pow]
  rw [div_eq_mul_inv]
  ring

/-- Weak growth keeps its original constant; its rate is divided by `b`. -/
theorem weak_power_bound (P : E →L[𝕜] E) (ι : E →L[𝕜] F) (b : ℝ) (hb : 0 < b)
    (C M : ℝ) (hbound : ∀ n x, ‖ι ((P ^ n) x)‖ ≤ C * M ^ n * ‖ι x‖) :
    ∀ n x, ‖weakEmbedding ι ((normalizedOperator P b ^ n) x)‖ ≤
      C * (M / b) ^ n * ‖weakEmbedding ι x‖ := by
  intro n x
  rw [norm_weak_normalizedOperator_pow_apply P ι b hb, norm_weakEmbedding_apply]
  calc
    _ ≤ (C * M ^ n * ‖ι x‖) / (weakScale ι * b ^ n) :=
      div_le_div_of_nonneg_right (hbound n x)
        (mul_nonneg (weakScale_pos ι).le (pow_nonneg hb.le n))
    _ = _ := by
      rw [div_pow]
      field_simp [(weakScale_pos ι).ne', hb.ne']

/-- Strong Lasota–Yorke growth rescales both rates. Rescaling the weak
inclusion multiplies the weak error constant by `weakScale ι`. -/
theorem strong_twoNorm_power_bound (P : E →L[𝕜] E) (ι : E →L[𝕜] F)
    (b : ℝ) (hb : 0 < b) (Cs Cw ρ M : ℝ)
    (hbound : ∀ n x, ‖(P ^ n) x‖ ≤ Cs * ρ ^ n * ‖x‖ + Cw * M ^ n * ‖ι x‖) :
    ∀ n x, ‖(normalizedOperator P b ^ n) x‖ ≤
      Cs * (ρ / b) ^ n * ‖x‖ + (Cw * weakScale ι) * (M / b) ^ n * ‖weakEmbedding ι x‖ := by
  intro n x
  rw [norm_normalizedOperator_pow_apply P b hb]
  calc
    _ ≤ (Cs * ρ ^ n * ‖x‖ + Cw * M ^ n * ‖ι x‖) / b ^ n :=
      div_le_div_of_nonneg_right (hbound n x) (pow_nonneg hb.le n)
    _ = _ := by
      rw [norm_weakEmbedding_apply, div_pow, div_pow]
      field_simp [(weakScale_pos ι).ne', hb.ne']

/-- If the original inequality uses one common constant, the normalized
inequality may use the common constant `C * weakScale ι`. -/
theorem common_twoNorm_power_bound (P : E →L[𝕜] E) (ι : E →L[𝕜] F)
    (b : ℝ) (hb : 0 < b) (C ρ M : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hbound : ∀ n x, ‖(P ^ n) x‖ ≤ C * ρ ^ n * ‖x‖ + C * M ^ n * ‖ι x‖) :
    ∀ n x, ‖(normalizedOperator P b ^ n) x‖ ≤
      (C * weakScale ι) * ((ρ / b) ^ n * ‖x‖ + (M / b) ^ n * ‖weakEmbedding ι x‖) := by
  intro n x
  have hcoeff : C ≤ C * weakScale ι := le_mul_of_one_le_right hC (weakScale_one_le ι)
  calc
    _ ≤ C * (ρ / b) ^ n * ‖x‖ +
        (C * weakScale ι) * (M / b) ^ n * ‖weakEmbedding ι x‖ :=
      strong_twoNorm_power_bound P ι b hb C C ρ M hbound n x
    _ ≤ (C * weakScale ι) * (ρ / b) ^ n * ‖x‖ +
        (C * weakScale ι) * (M / b) ^ n * ‖weakEmbedding ι x‖ := by
      gcongr
    _ = _ := by ring

/-- The strong contraction rate lies in `(0,1)` as soon as the reference
rate exceeds the original strong rate, even if the latter exceeds one. -/
theorem normalized_rate_pos_lt_one (ρ b : ℝ) (hρ : 0 < ρ) (hb : ρ < b) :
    0 < ρ / b ∧ ρ / b < 1 :=
  ⟨div_pos hρ (hρ.trans hb), (div_lt_one (hρ.trans hb)).mpr hb⟩

/-- Positive normalization also preserves the ordering of the two rates. -/
theorem normalized_rates_lt (ρ M b : ℝ) (hb : 0 < b) (hgap : ρ < M) :
    ρ / b < M / b := (div_lt_div_iff_of_pos_right hb).mpr hgap

/-- The real leading eigenvalue rescales by the same actual division. -/
theorem normalizedOperator_eigenvector (P : E →L[𝕜] E) (b r : ℝ) (v : E)
    (hv : P v = (r : 𝕜) • v) :
    normalizedOperator P b v = ((r / b : ℝ) : 𝕜) • v := by
  rw [normalizedOperator, smul_apply, hv, smul_smul]
  congr 1
  rw [div_eq_mul_inv, RCLike.ofReal_mul, mul_comm]

/-- Choosing `b` equal to the positive leading eigenvalue makes that
eigenvalue exactly one, rather than introducing a new spectral assumption. -/
theorem normalizedOperator_leading_fixed (P : E →L[𝕜] E) (b : ℝ) (hb : 0 < b) (v : E)
    (hv : P v = (b : 𝕜) • v) : normalizedOperator P b v = v := by
  rw [normalizedOperator_eigenvector P b b v hv, div_self hb.ne']
  simp only [RCLike.ofReal_one, one_smul]

/-- Exact operator-norm scaling of the strong-to-weak perturbation. -/
theorem norm_normalized_perturbation (P Q : E →L[𝕜] E) (ι : E →L[𝕜] F)
    (b : ℝ) (hb : 0 < b) :
    ‖(weakEmbedding ι).comp (normalizedOperator P b - normalizedOperator Q b)‖ =
      ‖ι.comp (P - Q)‖ / (b * weakScale ι) := by
  have he : (weakEmbedding ι).comp (normalizedOperator P b - normalizedOperator Q b) =
      ((((b * weakScale ι)⁻¹ : ℝ) : 𝕜)) • ι.comp (P - Q) := by
    ext x
    simp only [weakEmbedding, normalizedOperator, ContinuousLinearMap.comp_apply,
      smul_apply, sub_apply, map_sub, map_smul,
      smul_sub, smul_smul, mul_inv_rev, RCLike.ofReal_mul, mul_comm]
  rw [he, norm_smul, RCLike.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hb.le (weakScale_pos ι).le))]
  exact mul_comm _ _

/-- In particular a raw `D * ε^η` error becomes `D/(b*c) * ε^η`;
the argument `τ` can be any specified perturbation modulus. -/
theorem perturbation_bound (P Q : E →L[𝕜] E) (ι : E →L[𝕜] F)
    (b : ℝ) (hb : 0 < b) (D τ : ℝ) (hbound : ‖ι.comp (P - Q)‖ ≤ D * τ) :
    ‖(weakEmbedding ι).comp (normalizedOperator P b - normalizedOperator Q b)‖ ≤
      (D / (b * weakScale ι)) * τ := by
  rw [norm_normalized_perturbation P Q ι b hb]
  calc
    _ ≤ (D * τ) / (b * weakScale ι) :=
      div_le_div_of_nonneg_right hbound (mul_nonneg hb.le (weakScale_pos ι).le)
    _ = _ := by ring

end LeanShared.TwoNormNormalization
