module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rank stability under weak operator convergence and a uniform strong/weak
coercivity estimate on the ranges. The noisy projectors need not be finite
rank a priori. This is the rank-one part of KL's projector argument. -/

public noncomputable section
open ContinuousLinearMap Filter
open scoped Topology
namespace LeanShared.WeakProjectorRankStability
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A weakly close, range-coercive idempotent has a normalized rank-one
factorization. Its right vector is the image of the deterministic seed. -/
theorem factorization (P : E →L[ℂ] E) (i : E →L[ℂ] W)
    (ℓ₀ : E →L[ℂ] ℂ) (v : E) (hpair : ℓ₀ v = 1)
    (idempotent : P * P = P) (C δ : ℝ) (hC : 0 ≤ C)
    (small : C * δ < 1)
    (weakBound : ‖i.comp (P - ℓ₀.smulRight v)‖ ≤ δ)
    (seed : δ * ‖v‖ < ‖i v‖)
    (coercive : ∀ x, ‖P x‖ ≤ C * ‖i (P x)‖) :
    ∃ ℓ : E →L[ℂ] ℂ, ℓ (P v) = 1 ∧ P = ℓ.smulRight (P v) := by
  have bound (x : E) : ‖i ((P - ℓ₀.smulRight v) x)‖ ≤ δ * ‖x‖ :=
    ((i.comp (P - ℓ₀.smulRight v)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right weakBound (norm_nonneg x))
  have kernel (y : E) (hy : P y = y) (hℓy : ℓ₀ y = 0) : y = 0 := by
    have hweak : ‖i y‖ ≤ δ * ‖y‖ := by
      simpa only [sub_apply, smulRight_apply, hℓy, zero_smul, sub_zero, hy] using bound y
    have hstrong : ‖y‖ ≤ C * ‖i y‖ := by simpa only [hy] using coercive y
    have hh := mul_le_mul_of_nonneg_left hweak hC
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg y]
  have hw : P v ≠ 0 := by
    intro he
    have hh := bound v
    simp only [sub_apply, smulRight_apply, hpair, one_smul, he, zero_sub, map_neg, norm_neg] at hh
    exact seed.not_ge hh
  have hwfixed : P (P v) = P v := by
    have hh := congrArg (fun Q : E →L[ℂ] E => Q v) idempotent
    simpa only [mul_apply_eq_comp] using hh
  have ha : ℓ₀ (P v) ≠ 0 := by
    intro he
    exact hw (kernel (P v) hwfixed he)
  let ℓ := (ℓ₀ (P v))⁻¹ • (ℓ₀.comp P)
  have hnorm : ℓ (P v) = 1 := by simp [ℓ, hwfixed, ha]
  refine ⟨ℓ, hnorm, ?_⟩
  ext x
  apply sub_eq_zero.mp
  apply kernel
  · change P (P x - ℓ x • P v) = P x - ℓ x • P v
    rw [map_sub, map_smul, hwfixed]
    have hh := congrArg (fun Q : E →L[ℂ] E => Q x) idempotent
    simpa only [mul_apply_eq_comp] using congrArg (fun y => y - ℓ x • P v) hh
  · change ℓ₀ (P x - ℓ x • P v) = 0
    simp only [ℓ, map_sub, map_smul, smul_apply, comp_apply, smul_eq_mul]
    field_simp [ha]
    ring

/-- Weak convergence plus uniform range coercivity preserves rank one on a
parameter neighbourhood, without assuming finite rank of the approximants. -/
theorem eventually_factorization {ι : Type*} {l : Filter ι}
    (P : ι → E →L[ℂ] E) (i : E →L[ℂ] W) (hi : Function.Injective i)
    (ℓ₀ : E →L[ℂ] ℂ) (v : E) (hpair : ℓ₀ v = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (weakConvergence : Tendsto (fun ε => i.comp (P ε - ℓ₀.smulRight v)) l (𝓝 0))
    (projections : ∀ᶠ ε in l, P ε * P ε = P ε ∧ ∀ x, ‖P ε x‖ ≤ C * ‖i (P ε x)‖) :
    ∀ᶠ ε in l, ∃ ℓ : E →L[ℂ] ℂ, ℓ (P ε v) = 1 ∧ P ε = ℓ.smulRight (P ε v) := by
  have hv : v ≠ 0 := by intro he; exact zero_ne_one (by simpa only [he, map_zero] using hpair)
  have hiv : i v ≠ 0 := by intro he; exact hv (hi (by simpa using he))
  have smallC : ∀ᶠ ε in l, C * ‖i.comp (P ε - ℓ₀.smulRight v)‖ < 1 := by
    have hh := weakConvergence.norm.const_mul C
    have hh' : Tendsto (fun ε => C * ‖i.comp (P ε - ℓ₀.smulRight v)‖) l (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using hh
    exact hh'.eventually (gt_mem_nhds zero_lt_one)
  have smallSeed : ∀ᶠ ε in l, ‖i.comp (P ε - ℓ₀.smulRight v)‖ * ‖v‖ < ‖i v‖ := by
    have hh := weakConvergence.norm.mul_const ‖v‖
    have hh' : Tendsto (fun ε => ‖i.comp (P ε - ℓ₀.smulRight v)‖ * ‖v‖) l (𝓝 0) := by
      simpa only [norm_zero, zero_mul] using hh
    exact hh'.eventually (gt_mem_nhds (norm_pos_iff.mpr hiv))
  filter_upwards [projections, smallC, smallSeed] with ε hp hc hs
  exact factorization (P ε) i ℓ₀ v hpair hp.1 C ‖i.comp (P ε - ℓ₀.smulRight v)‖
    hC hc le_rfl hs hp.2

end LeanShared.WeakProjectorRankStability
