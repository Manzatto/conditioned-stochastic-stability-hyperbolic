module

public import LeanShared.Analysis.DyadicSymbols
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The manuscript's radial and angular cone multiplier bases

Only the existence of a smooth radial cutoff and a smooth angular extension
near the unit sphere is an input. The actual multipliers are constructed;
their smoothness at the origin and compact support are derived. The positive
branch is `true`, the negative branch `false`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff SchwartzMap Topology

namespace LeanShared.ConeDyadicSymbols

/-- The smooth cutoff data stated in the manuscript, with existence left classical. -/
structure RadialCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  one : ∀ r, |r| ≤ 1 → toFun r = 1
  zero : ∀ r, 2 ≤ |r| → toFun r = 0
  even : ∀ r, toFun (-r) = toFun r
  nonneg : ∀ r, 0 ≤ toFun r
  le_one : ∀ r, toFun r ≤ 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalized (ξ : E) : E := ‖ξ‖⁻¹ • ξ

theorem norm_normalized {ξ : E} (hξ : ξ ≠ 0) : ‖normalized ξ‖ = 1 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  simp only [normalized, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ (ne_of_gt hn)]

theorem normalized_smoothAt {ξ : E} (hξ : ξ ≠ 0) : ContDiffAt ℝ ∞ normalized ξ :=
  ((contDiffAt_norm ℝ hξ).inv (norm_ne_zero_iff.mpr hξ)).smul contDiffAt_id

theorem normalized_pos_smul (r : ℝ) (hr : 0 < r) (ξ : E) : normalized (r • ξ) = normalized ξ := by
  simp only [normalized, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul,
    mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), mul_one]

/-- A smooth ambient extension of the sphere cutoff. Its existence and cone
separation are the classical angular-cutoff input, not multiplier smoothness. -/
structure AngularCutoff (Cplus Cminus : Set E) where
  toFun : E → ℝ
  smoothAt_unit : ∀ ξ, ‖ξ‖ = 1 → ContDiffAt ℝ ∞ toFun ξ
  nonneg_unit : ∀ ξ, ‖ξ‖ = 1 → 0 ≤ toFun ξ
  le_one_unit : ∀ ξ, ‖ξ‖ = 1 → toFun ξ ≤ 1
  one_on : ∀ ξ ∈ Cplus, ‖ξ‖ = 1 → toFun ξ = 1
  zero_on : ∀ ξ ∈ Cminus, ‖ξ‖ = 1 → toFun ξ = 0

def radial (χ : RadialCutoff) (ξ : E) : ℝ := χ.toFun ‖ξ‖

theorem radial_smooth (χ : RadialCutoff) : ContDiff ℝ ∞ (radial (E := E) χ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with y hy
    apply χ.one
    have hn : ‖y‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    simpa only [abs_of_nonneg (norm_nonneg y)] using hn.le
  · exact χ.smooth.contDiffAt.comp ξ (contDiffAt_norm ℝ hξ)

def annular (χ : RadialCutoff) (ξ : E) : ℝ := radial χ ξ - radial χ ((2 : ℝ) • ξ)

theorem annular_smooth (χ : RadialCutoff) : ContDiff ℝ ∞ (annular (E := E) χ) :=
  (radial_smooth χ).sub ((radial_smooth χ).comp (contDiff_id.const_smul (2 : ℝ)))

theorem annular_zero_near_origin (χ : RadialCutoff) {ξ : E} (hξ : ‖ξ‖ ≤ 1 / 2) :
    annular χ ξ = 0 := by
  have h1 : χ.toFun ‖ξ‖ = 1 := χ.one _ (by rw [abs_of_nonneg (norm_nonneg _)]; linarith)
  have h2 : χ.toFun ‖(2 : ℝ) • ξ‖ = 1 := by
    apply χ.one
    rw [abs_of_nonneg (norm_nonneg _), norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  simp only [annular, radial, h1, h2, sub_self]

omit [InnerProductSpace ℝ E] in
theorem radial_zero_outside (χ : RadialCutoff) {ξ : E} (hξ : 2 ≤ ‖ξ‖) : radial χ ξ = 0 :=
  χ.zero _ (by simpa only [abs_of_nonneg (norm_nonneg _)] using hξ)

theorem annular_zero_outside (χ : RadialCutoff) {ξ : E} (hξ : 2 ≤ ‖ξ‖) : annular χ ξ = 0 := by
  rw [annular, radial_zero_outside χ hξ, radial_zero_outside χ]
  · exact sub_self _
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

def angle (Φ : E → ℝ) (s : Bool) (ξ : E) : ℝ :=
  if s then Φ (normalized ξ) else 1 - Φ (normalized ξ)

theorem angle_smoothAt {Cplus Cminus : Set E} (Φ : AngularCutoff Cplus Cminus)
    (s : Bool) {ξ : E} (hξ : ξ ≠ 0) : ContDiffAt ℝ ∞ (angle Φ.toFun s) ξ := by
  have hh := (Φ.smoothAt_unit _ (norm_normalized hξ)).comp ξ (normalized_smoothAt hξ)
  cases s
  · exact contDiffAt_const.sub hh
  · exact hh

def low (χ : RadialCutoff) : E → ℂ := fun ξ => (radial χ ξ : ℂ) / 2

def highReal (χ : RadialCutoff) (Φ : E → ℝ) (s : Bool) (ξ : E) : ℝ :=
  angle Φ s ξ * annular χ ξ

def high (χ : RadialCutoff) (Φ : E → ℝ) (s : Bool) : E → ℂ :=
  fun ξ => (highReal χ Φ s ξ : ℂ)

theorem highReal_smooth {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) (s : Bool) : ContDiff ℝ ∞ (highReal χ Φ.toFun s) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hn : ‖y‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    simp only [highReal, annular_zero_near_origin χ hn.le, mul_zero]
  · exact (angle_smoothAt Φ s hξ).mul (annular_smooth χ).contDiffAt

theorem low_smooth (χ : RadialCutoff) : ContDiff ℝ ∞ (low (E := E) χ) :=
  (Complex.ofRealCLM.contDiff.comp (radial_smooth χ)).div_const 2

theorem high_smooth {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) (s : Bool) : ContDiff ℝ ∞ (high χ Φ.toFun s) :=
  Complex.ofRealCLM.contDiff.comp (highReal_smooth χ Φ s)

variable [FiniteDimensional ℝ E]

theorem low_hasCompactSupport (χ : RadialCutoff) : HasCompactSupport (low (E := E) χ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E) 2)
  intro ξ hξ
  have hn : 2 < ‖ξ‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hξ
  simp only [low, radial_zero_outside χ hn.le, Complex.ofReal_zero, zero_div]

theorem high_hasCompactSupport (χ : RadialCutoff) (Φ : E → ℝ) (s : Bool) :
    HasCompactSupport (high χ Φ s) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E) 2)
  intro ξ hξ
  have hn : 2 < ‖ξ‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hξ
  simp only [high, highReal, annular_zero_outside χ hn.le, mul_zero, Complex.ofReal_zero]

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual symbols of the manuscript, with smoothness and support proved. -/
def symbols {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) :
    ℕ × Bool → 𝓢(E, ℂ) :=
  DyadicSymbols.symbolsFromMultipliers (fun _ : Bool => low χ) (high χ Φ.toFun)
    (fun _ => low_hasCompactSupport χ) (high_hasCompactSupport χ Φ.toFun)
    (fun _ => low_smooth χ) (high_smooth χ Φ)

/-- The genuine manuscript-convention Fourier kernel family for the cone symbols. -/
def kernels {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) :
    ℕ × Bool → 𝓢(E, ℂ) := fun j => FourierSchwartzKernel.kernel (symbols χ Φ j)

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbols_hasCompactSupport {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) (j : ℕ × Bool) : HasCompactSupport (symbols χ Φ j : E → ℂ) :=
  DyadicSymbols.symbolsFromMultipliers_hasCompactSupport (fun _ : Bool => low χ) (high χ Φ.toFun)
    (fun _ => low_hasCompactSupport χ) (high_hasCompactSupport χ Φ.toFun)
    (fun _ => low_smooth χ) (high_smooth χ Φ) j

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbols_apply_zero {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) (s : Bool) (ξ : E) :
    symbols χ Φ (0, s) ξ = (χ.toFun ‖ξ‖ : ℂ) / 2 := rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The exact radial/angular formula: inverse natural powers represent `2⁻ⁿ`. -/
theorem symbols_apply_of_ne_zero {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) (j : ℕ × Bool) (hj : j.1 ≠ 0) (ξ : E) :
    symbols χ Φ j ξ = (angle Φ.toFun j.2 ξ : ℂ) *
      ((χ.toFun (((2 : ℝ) ^ j.1)⁻¹ * ‖ξ‖) -
        χ.toFun ((2 * ((2 : ℝ) ^ j.1)⁻¹) * ‖ξ‖) : ℝ) : ℂ) := by
  change DyadicSymbols.symbol
    (fun s : Bool => FourierSchwartzKernel.symbol (low χ) (low_hasCompactSupport χ) (low_smooth χ))
    (fun s => FourierSchwartzKernel.symbol (high χ Φ.toFun s)
      (high_hasCompactSupport χ Φ.toFun s) (high_smooth χ Φ s)) j ξ = _
  rw [DyadicSymbols.symbol_apply_of_ne_zero _ _ j hj, FourierSchwartzKernel.symbol_apply]
  have hr : 0 < ((2 : ℝ) ^ j.1)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) _)
  simp only [high, highReal, angle, normalized_pos_smul _ hr, annular, radial,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    ← mul_assoc, Complex.ofReal_mul]

theorem kernels_uniform_L1 {Cplus Cminus : Set E} (χ : RadialCutoff)
    (Φ : AngularCutoff Cplus Cminus) : ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ × Bool,
      (∫ x : E, ‖kernels χ Φ j x‖) ≤ A :=
  DyadicSymbols.fromMultipliers_uniform_L1 (fun _ : Bool => low χ) (high χ Φ.toFun)
    (fun _ => low_hasCompactSupport χ) (high_hasCompactSupport χ Φ.toFun)
    (fun _ => low_smooth χ) (high_smooth χ Φ)

end LeanShared.ConeDyadicSymbols
