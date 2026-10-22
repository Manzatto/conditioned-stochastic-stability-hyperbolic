module

public import LeanShared.Analysis.ResolventNeumannSeries
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Norm-convergent Neumann expansion throughout the exterior spectral
disk. The radius is enlarged by analytic uniqueness and the proved
complex spectral-radius theory. -/

public noncomputable section
open Set
open scoped NNReal ENNReal

namespace LeanShared.SpectralRadiusNeumannSeries
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem hasSum (a : A) (z : ℂ) (outside : spectralRadius ℂ a < (‖z‖₊ : ℝ≥0∞)) :
    HasSum (fun n : ℕ => z⁻¹ • (z⁻¹ • a) ^ n) (resolvent a z) := by
  have hz0 : z ≠ 0 := by
    intro zero
    simp only [zero, nnnorm_zero, ENNReal.coe_zero, not_lt_zero] at outside
  have inverseRadius : (‖z⁻¹‖₊ : ℝ≥0∞) < (spectralRadius ℂ a)⁻¹ := by
    rw [nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hz0)]
    exact ENNReal.inv_lt_inv.mpr outside
  obtain ⟨r, inside, smaller⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp inverseRadius
  have positiveR : 0 < r := by
    apply ENNReal.coe_lt_coe.mp
    exact lt_of_le_of_lt zero_le inside
  have series := (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius
    ((spectrum.differentiableOn_inverse_one_sub_smul smaller).hasFPowerSeriesOnBall positiveR)
  have insideBall : z⁻¹ ∈ Metric.eball (0 : ℂ) (r : ℝ≥0∞) := by
    change edist z⁻¹ 0 < (r : ℝ≥0∞)
    simpa only [edist_nndist, nndist_zero_right] using inside
  have sum : HasSum (fun n : ℕ => (z⁻¹ • a) ^ n)
      (Ring.inverse (1 - z⁻¹ • a)) := by
    simpa only [ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_pow, zero_add] using series.hasSum insideBall
  have unit := spectrum.isUnit_one_sub_smul_of_lt_inv_radius inverseRadius
  let B := z⁻¹ • Ring.inverse (1 - z⁻¹ • a)
  have shift : z • (1 - z⁻¹ • a) = algebraMap ℂ A z - a := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul,
      Algebra.algebraMap_eq_smul_one]
  have left : (algebraMap ℂ A z - a) * B = 1 := by
    rw [← shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    exact Ring.mul_inverse_cancel _ unit
  have formula : resolvent a z = B :=
    left_inv_eq_right_inv (Ring.inverse_mul_cancel _
      (spectrum.mem_resolventSet_of_spectralRadius_lt outside)) left
  rw [formula]
  exact sum.const_smul z⁻¹

end LeanShared.SpectralRadiusNeumannSeries
