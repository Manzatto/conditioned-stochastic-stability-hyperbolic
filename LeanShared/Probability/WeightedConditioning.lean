module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-!
# Departure weights and scalar normalization

A bounded nonnegative departure weight can be divided by any positive upper
bound to give a sub-Markov kernel. The corresponding finite transfer words
acquire exactly one scalar factor per transition. Ratios conditioned on
survival are consequently unchanged, including at a zero denominator under
Lean's totalized division.

The kernel results require measurability and an explicit mass bound. The
algebraic word results use Bochner integrals directly and do not assume
boundedness or integrability: scalar homogeneity also holds for their
totalized values. Connecting words to path expectations requires the usual
bounded measurable Feynman–Kac hypotheses, and is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LeanShared.WeightedConditioning

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Multiply each transition measure by a measurable weight at its departure. -/
def departureKernel (K : Kernel X Y) (w : X → ℝ≥0∞) (hw : Measurable w) : Kernel X Y where
  toFun x := w x • K x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hw.mul (K.measurable_coe hs)

@[simp]
theorem departureKernel_apply (K : Kernel X Y) (w : X → ℝ≥0∞)
    (hw : Measurable w) (x : X) : departureKernel K w hw x = w x • K x := rfl

@[simp]
theorem departureKernel_apply_set (K : Kernel X Y) (w : X → ℝ≥0∞)
    (hw : Measurable w) (x : X) (s : Set Y) :
    departureKernel K w hw x s = w x * K x s := by
  simp [departureKernel, Measure.smul_apply]

/-- Real nonnegative weights are represented by `ENNReal.ofReal`. -/
def realWeightedKernel (K : Kernel X Y) (w : X → ℝ) (hw : Measurable w) : Kernel X Y :=
  departureKernel K (fun x => ENNReal.ofReal (w x)) hw.ennreal_ofReal

@[simp]
theorem realWeightedKernel_apply (K : Kernel X Y) (w : X → ℝ)
    (hw : Measurable w) (x : X) :
    realWeightedKernel K w hw x = ENNReal.ofReal (w x) • K x := rfl

/-- Normalize a real departure weight by a constant, with no hidden bound. -/
def normalizedKernel (K : Kernel X Y) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) : Kernel X Y :=
  realWeightedKernel K (fun x => w x / R) (hw.div_const R)

omit [MeasurableSpace X] in
/-- A positive upper bound makes the normalized weight lie in `[0,1]`. -/
theorem normalizedWeight_le_one (w : X → ℝ) {R : ℝ} (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (x : X) : ENNReal.ofReal (w x / R) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((div_le_one hR).mpr (hwR x))

/-- Normalizing a bounded departure weight preserves the sub-Markov mass bound. -/
theorem normalizedKernel_mass_le_one (K : Kernel X Y) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hK : ∀ x, K x univ ≤ 1) (x : X) :
    normalizedKernel K w R hw x univ ≤ 1 := by
  change (ENNReal.ofReal (w x / R) • K x) univ ≤ 1
  rw [Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul' (normalizedWeight_le_one w hR hwR x) (hK x)).trans (by simp)

/-- In particular the normalized kernel is uniformly finite. -/
theorem normalizedKernel_isFinite (K : Kernel X Y) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hK : ∀ x, K x univ ≤ 1) : IsFiniteKernel (normalizedKernel K w R hw) := by
  exact ⟨⟨1, by simp, normalizedKernel_mass_le_one K w R hw hR hwR hK⟩⟩

/-- The exact scalar relation between the normalized and unnormalized measures. -/
theorem normalizedKernel_apply_eq (K : Kernel X Y) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hR : 0 < R) (x : X) :
    normalizedKernel K w R hw x = ENNReal.ofReal R⁻¹ • realWeightedKernel K w hw x := by
  simp only [normalizedKernel, realWeightedKernel_apply, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm (w x) R⁻¹,
    ENNReal.ofReal_mul (inv_nonneg.mpr hR.le)]

/-- Integration against the weighted kernel is the departure-weighted transfer. -/
theorem integral_realWeightedKernel (K : Kernel X Y) (w : X → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (f : Y → ℝ) (x : X) :
    (∫ y, f y ∂realWeightedKernel K w hw x) = w x * ∫ y, f y ∂K x := by
  rw [realWeightedKernel_apply, integral_smul_measure, ENNReal.toReal_ofReal (hw0 x),
    smul_eq_mul]

section Words

variable (K : Kernel X X)

/-- The finite weighted word `φ₀ w K ⋯ φₙ₋₁ w K v`, built from the right. -/
def word (w : X → ℝ) (φ : ℕ → X → ℝ) : ℕ → (X → ℝ) → X → ℝ
  | 0, v => v
  | n + 1, v => word w φ n (fun x => φ n x * w x * ∫ y, v y ∂K x)

/-- Terminal scalar homogeneity, with no integrability assumption. -/
theorem word_const_mul (w : X → ℝ) (φ : ℕ → X → ℝ)
    (n : ℕ) (v : X → ℝ) (c : ℝ) :
    word K w φ n (fun x => c * v x) = fun x => c * word K w φ n v x := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [word, integral_const_mul]
      have he : (fun x => φ n x * w x * (c * ∫ y, v y ∂K x)) =
          (fun x => c * (φ n x * w x * ∫ y, v y ∂K x)) := by
        funext x
        ring
      rw [he, ih]

/-- A uniform change in departure weight contributes exactly `c^n` at horizon `n`. -/
theorem word_scaled_weight (w : X → ℝ) (φ : ℕ → X → ℝ)
    (n : ℕ) (v : X → ℝ) (c : ℝ) :
    word K (fun x => c * w x) φ n v = fun x => c ^ n * word K w φ n v x := by
  induction n generalizing v with
  | zero => simp [word]
  | succ n ih =>
      simp only [word]
      rw [ih]
      have he : (fun x => φ n x * (c * w x) * ∫ y, v y ∂K x) =
          (fun x => c * (φ n x * w x * ∫ y, v y ∂K x)) := by
        funext x
        ring
      rw [he, word_const_mul]
      funext x
      simp only [pow_succ]
      ring

/-- A finite-horizon survival-normalized weighted observation word. -/
def conditionedWord (w : X → ℝ) (φ : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  word K w φ n (fun _ => 1) x / word K w (fun _ _ => 1) n (fun _ => 1) x

/-- The scalar cancels exactly, including at a null finite-horizon survival mass. -/
theorem conditionedWord_scaled_weight (w : X → ℝ) (φ : ℕ → X → ℝ)
    (n : ℕ) (x : X) (c : ℝ) (hc : c ≠ 0) :
    conditionedWord K (fun y => c * w y) φ n x = conditionedWord K w φ n x := by
  simp only [conditionedWord, word_scaled_weight]
  exact mul_div_mul_left _ _ (pow_ne_zero n hc)

/-- Dividing the weight by a positive upper bound does not change conditional ratios. -/
theorem conditionedWord_normalized_weight (w : X → ℝ) (φ : ℕ → X → ℝ)
    (n : ℕ) (x : X) (R : ℝ) (hR : 0 < R) :
    conditionedWord K (fun y => w y / R) φ n x = conditionedWord K w φ n x := by
  have he : (fun y => w y / R) = fun y => R⁻¹ * w y := by
    funext y
    rw [div_eq_mul_inv, mul_comm]
  rw [he]
  exact conditionedWord_scaled_weight K w φ n x R⁻¹ (inv_ne_zero hR.ne')

end Words

end LeanShared.WeightedConditioning
