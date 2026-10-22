module

public import LeanShared.Analysis.ExponentialCoefficientSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The finite spectral determinant is the exponential of its power-sum
trace series. This supplies the finite spectral factor used in the
determinant--spectrum argument; no infinite-dimensional trace identity
is assumed here. -/

public noncomputable section
open scoped BigOperators

namespace LeanShared.FiniteExponentialDeterminant
open ExponentialCoefficientSeries

variable {ι : Type*} [Fintype ι]

/-- Literal logarithmic power-sum coefficients sum to the finite sum of
logarithms on the common convergence disk. -/
theorem hasSum_logarithmic (values : ι → ℂ) (z : ℂ)
    (small : ∀ i, ‖z * values i‖ < 1) :
    HasSum (fun n => logarithmicCoefficient (fun k => ∑ i, values i ^ k) n * z ^ n)
      (∑ i, Complex.log (1 - z * values i)) := by
  classical
  have each (i : ι) : HasSum (fun n : ℕ => -(z * values i) ^ n / (n : ℂ))
      (Complex.log (1 - z * values i)) := by
    simpa only [neg_neg, neg_div] using
      (Complex.hasSum_taylorSeries_neg_log (small i)).neg
  have sums := hasSum_sum (s := Finset.univ) (fun i _ => each i)
  convert sums using 1
  funext n
  have terms (i : ι) : -(z * values i) ^ n / (n : ℂ) =
      (-values i ^ n / (n : ℂ)) * z ^ n := by
    rw [mul_pow]
    ring
  simp only [terms, logarithmicCoefficient, ← Finset.sum_mul,
    ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The exponential trace series is exactly the finite spectral product. -/
theorem correction_eq_product (values : ι → ℂ) (z : ℂ)
    (small : ∀ i, ‖z * values i‖ < 1) :
    correction (fun n => ∑ i, values i ^ n) z = ∏ i, (1 - z * values i) := by
  rw [correction, (hasSum_logarithmic values z small).tsum_eq, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  apply Complex.exp_log
  exact sub_ne_zero.mpr (fun h => by
    have := small i
    rw [← h, norm_one] at this
    exact (lt_irrefl _ this))

/-- The finite product supplies the entire continuation of its trace germ. -/
theorem product_analytic (values : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∏ i, (1 - z * values i)) Set.univ := by
  classical
  have finite (s : Finset ι) :
      AnalyticOnNhd ℂ (fun z : ℂ => ∏ i ∈ s, (1 - z * values i)) Set.univ := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (analyticOnNhd_const.sub (analyticOnNhd_id.mul analyticOnNhd_const)).mul ih
  exact finite Finset.univ

/-- All zeros of the finite spectral factor are reciprocal eigenvalues,
including repeated values in the original indexed spectrum. -/
theorem product_eq_zero_iff (values : ι → ℂ) (z : ℂ) (hz : z ≠ 0) :
    (∏ i, (1 - z * values i)) = 0 ↔ ∃ i, values i = z⁻¹ := by
  classical
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨i, ?_⟩
    apply mul_left_cancel₀ hz
    rw [mul_inv_cancel₀ hz]
    exact (sub_eq_zero.mp hi).symm
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ _, by simp only [hi, mul_inv_cancel₀ hz, sub_self]⟩

/-- Application to the actual powers, trace and determinant of a diagonal
matrix. The trace sequence is computed rather than supplied as an input. -/
theorem diagonal_trace_determinant [DecidableEq ι] (values : ι → ℂ) (z : ℂ)
    (small : ∀ i, ‖z * values i‖ < 1) :
    correction (fun n => Matrix.trace ((Matrix.diagonal values) ^ n)) z =
      Matrix.det (1 - z • Matrix.diagonal values) := by
  have traces (n : ℕ) : Matrix.trace ((Matrix.diagonal values) ^ n) =
      ∑ i, values i ^ n := by
    simp only [Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]
  have matrix : (1 - z • Matrix.diagonal values : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => 1 - z * values i) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_sub]
    rfl
  simp only [traces, matrix, Matrix.det_diagonal]
  exact correction_eq_product values z small

end LeanShared.FiniteExponentialDeterminant
