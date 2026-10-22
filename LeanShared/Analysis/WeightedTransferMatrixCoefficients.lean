module

public import LeanShared.Analysis.InvariantFiniteRegularCompatibility
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Actual weighted-transfer powers as continuous matrix coefficients

The seed representing the departure weight gives the length `n + 1` weighted
integral after `n` transfer steps. This avoids using the constant function as
an element of a space of functions supported in a proper neighbourhood.
The completed operator is linked to the finite-regular operator by its actual
intertwining identity; no spectral property is assumed here.
-/

public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LeanShared.InvariantFiniteRegularTransfer

variable {X Ω R B : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f,
    FiniteRegularTransferRealization.weightedComposition (F a) g (view f) ∈ view.range)
  (C : ℝ) (hbound : ∀ a f, ‖action view hview F g hregular a f‖ ≤ C * ‖f‖)

/-- Every finite-regular iterate is the literal product of departure weights,
with the original input evaluated at the final time. -/
theorem operator_pow_function (a : Ω) (n : ℕ) (f : R) (x : X) :
    view (((operator view hview F g hregular C hbound a) ^ n) f) x =
      ((∏ j ∈ Finset.range n, g ((F a)^[j] x) : ℝ) : ℂ) *
        view f ((F a)^[n] x) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, operator_function,
      Finset.prod_range_succ, Complex.ofReal_mul, Function.iterate_succ_apply']
    exact (mul_assoc _ _ _).symm

/-- The admissible weight seed replaces the generally unavailable constant
function, at the cost of exactly one additional departure weight. -/
theorem operator_pow_weight (a : Ω) (seed : R)
    (hseed : ∀ x, view seed x = (g x : ℂ)) (n : ℕ) (x : X) :
    view (((operator view hview F g hregular C hbound a) ^ n) seed) x =
      ((∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x) : ℝ) : ℂ) := by
  rw [operator_pow_function, hseed, Finset.prod_range_succ, Complex.ofReal_mul]

variable (realize : R →L[ℂ] B) (P : B →L[ℂ] B) (a : Ω)

/-- The proved one-step compatibility propagates to all powers, with the same
finite-regular seed and the same completed operator. -/
theorem realize_operator_pow
    (compatibility : realize.comp (operator view hview F g hregular C hbound a) =
      P.comp realize) (n : ℕ) (f : R) :
    (P ^ n) (realize f) =
      realize (((operator view hview F g hregular C hbound a) ^ n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp]
    have hone := congrArg (fun L : R →L[ℂ] B => L f) compatibility
    change realize (operator view hview F g hregular C hbound a f) = P (realize f) at hone
    rw [← hone, ih, pow_succ, mul_apply_eq_comp]

/-- Exact distribution-test pairing for powers of the actual completed
operator, using the weight as its initial supported function. -/
theorem integral_weight_product_eq_matrixCoefficient [MeasurableSpace X]
    (μ : Measure X) (test : X → ℂ) (pairing : B →L[ℂ] ℂ)
    (hpairing : ∀ f : R, pairing (realize f) = ∫ x, view f x * test x ∂μ)
    (compatibility : realize.comp (operator view hview F g hregular C hbound a) =
      P.comp realize)
    (seed : R) (hseed : ∀ x, view seed x = (g x : ℂ)) (n : ℕ) :
    (∫ x, (((∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x) : ℝ) : ℂ) * test x) ∂μ) =
      pairing ((P ^ n) (realize seed)) := by
  rw [realize_operator_pow view hview F g hregular C hbound realize P a compatibility,
    hpairing]
  congr 1
  funext x
  rw [operator_pow_weight view hview F g hregular C hbound a seed hseed]

/-- The matrix-coefficient bound needed to turn geometric integral growth
into a lower bound on the norm growth of this exact operator. -/
theorem norm_integral_weight_product_le [MeasurableSpace X]
    (μ : Measure X) (test : X → ℂ) (pairing : B →L[ℂ] ℂ)
    (hpairing : ∀ f : R, pairing (realize f) = ∫ x, view f x * test x ∂μ)
    (compatibility : realize.comp (operator view hview F g hregular C hbound a) =
      P.comp realize)
    (seed : R) (hseed : ∀ x, view seed x = (g x : ℂ)) (n : ℕ) :
    ‖∫ x, (((∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x) : ℝ) : ℂ) * test x) ∂μ‖ ≤
      ‖pairing‖ * ‖P ^ n‖ * ‖realize seed‖ := by
  rw [integral_weight_product_eq_matrixCoefficient view hview F g hregular C hbound
    realize P a μ test pairing hpairing compatibility seed hseed n]
  calc
    ‖pairing ((P ^ n) (realize seed))‖ ≤ ‖pairing‖ * ‖(P ^ n) (realize seed)‖ :=
      pairing.le_opNorm _
    _ ≤ ‖pairing‖ * (‖P ^ n‖ * ‖realize seed‖) :=
      mul_le_mul_of_nonneg_left ((P ^ n).le_opNorm _) (norm_nonneg _)
    _ = ‖pairing‖ * ‖P ^ n‖ * ‖realize seed‖ := (mul_assoc _ _ _).symm

/-- The nonnegative geometric lower-growth integral is the extended-real
norm of this same continuous matrix coefficient. -/
theorem lintegral_weight_product_eq_ofReal_norm [MeasurableSpace X]
    (μ : Measure X) (pairing : B →L[ℂ] ℂ)
    (hpairing : ∀ f : R, pairing (realize f) = ∫ x, view f x ∂μ)
    (compatibility : realize.comp (operator view hview F g hregular C hbound a) =
      P.comp realize)
    (seed : R) (hseed : ∀ x, view seed x = (g x : ℂ))
    (nonnegative : ∀ x, 0 ≤ g x) (n : ℕ)
    (integrable : Integrable
      (fun x => ∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x)) μ) :
    (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x)) ∂μ) =
      ENNReal.ofReal ‖pairing ((P ^ n) (realize seed))‖ := by
  have identity := integral_weight_product_eq_matrixCoefficient view hview F g hregular
    C hbound realize P a μ (fun _ => 1) pairing
    (by intro f; simpa only [mul_one] using hpairing f) compatibility seed hseed n
  simp only [mul_one] at identity
  have nonnegativeProduct (x : X) :
      0 ≤ ∏ j ∈ Finset.range (n + 1), g ((F a)^[j] x) :=
    Finset.prod_nonneg (fun _ _ => nonnegative _)
  rw [← identity, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg nonnegativeProduct)]
  exact (ofReal_integral_eq_lintegral_ofReal integrable
    (Filter.Eventually.of_forall nonnegativeProduct)).symm

end LeanShared.InvariantFiniteRegularTransfer

namespace LeanShared.WeightedOrbitIntegrals

/-- Positive-length departure-weight products vanish outside the weight's
domain already at time zero. Thus restricting the reference measure to the
actual collar leaves the geometric growth integral unchanged. -/
theorem lintegral_eq_subtype_comap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (g : X → ℝ) (K : Set X)
    (measurableK : MeasurableSet K) (outside : ∀ x, x ∉ K → g x = 0) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), g (T^[j] x)) ∂μ) =
      ∫⁻ x : K, ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), g (T^[j] x.val))
        ∂μ.comap Subtype.val := by
  let f := fun x => ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), g (T^[j] x))
  change (∫⁻ x, f x ∂μ) = ∫⁻ x : K, f x.val ∂μ.comap Subtype.val
  rw [MeasureTheory.lintegral_subtype_comap measurableK f,
    ← MeasureTheory.lintegral_indicator measurableK]
  apply MeasureTheory.lintegral_congr
  intro x
  by_cases hx : x ∈ K
  · simp only [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    dsimp only [f]
    have zeroProduct : (∏ j ∈ Finset.range (n + 1), g (T^[j] x)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa only [Function.iterate_zero, id_eq] using outside x hx
    rw [zeroProduct, ENNReal.ofReal_zero]

end LeanShared.WeightedOrbitIntegrals
