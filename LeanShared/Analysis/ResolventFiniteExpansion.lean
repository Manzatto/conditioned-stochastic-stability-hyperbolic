module

public import LeanShared.Analysis.TwoNormSpectralShift
import all LeanShared.Analysis.TwoNormSpectralShift
public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! A finite resolvent expansion valid throughout the resolvent set, without
a one-step Neumann norm assumption. -/

public section
open ContinuousLinearMap
namespace LeanShared.ResolventFiniteExpansion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Exact finite expansion of the actual resolvent into a shifted-power
remainder and an explicit polynomial. -/
theorem formula (T : E →L[ℂ] E) (z : ℂ) (hz : z ≠ 0)
    (hres : z ∈ resolventSet ℂ T) (n : ℕ) :
    resolvent T z = (z ^ n)⁻¹ •
      (resolvent T z * T ^ n + TwoNormSpectralShift.powerSum T z n) := by
  let Q := resolvent T z
  let P := TwoNormSpectralShift.powerSum T z n
  have factor : (T - z • 1) * P = T ^ n - (z ^ n) • 1 := by
    have comm : Commute T (z • (1 : E →L[ℂ] E)) := by
      change T * (z • 1) = (z • 1) * T
      simpa only [Algebra.algebraMap_eq_smul_one] using (Algebra.commutes z T).symm
    simpa only [P, TwoNormSpectralShift.powerSum, smul_pow, one_pow] using comm.mul_geom_sum₂ n
  have right : Q * (T - z • 1) = -1 := by
    have hh : Q * (z • 1 - T) = 1 := Ring.inverse_mul_cancel _ hres
    calc
      Q * (T - z • 1) = Q * (-(z • 1 - T)) := by rw [neg_sub]
      _ = -(Q * (z • 1 - T)) := mul_neg _ _
      _ = -1 := congrArg Neg.neg hh
  have identity : Q * T ^ n - (z ^ n) • Q = -P := by
    calc
      _ = Q * (T ^ n - (z ^ n) • 1) := by rw [mul_sub, mul_smul_comm, mul_one]
      _ = Q * ((T - z • 1) * P) := by rw [factor]
      _ = (Q * (T - z • 1)) * P := (mul_assoc _ _ _).symm
      _ = -P := by rw [right, neg_one_mul]
  have rearranged : (z ^ n) • Q = Q * T ^ n + P := by
    have hh : (z ^ n) • Q - Q * T ^ n = P := by rw [← neg_sub, identity, neg_neg]
    calc
      _ = ((z ^ n) • Q - Q * T ^ n) + Q * T ^ n := by abel
      _ = _ := by rw [hh, add_comm]
  change Q = (z ^ n)⁻¹ • (Q * T ^ n + P)
  rw [← rearranged, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hz), one_smul]

end LeanShared.ResolventFiniteExpansion
