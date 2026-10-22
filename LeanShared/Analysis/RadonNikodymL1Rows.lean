module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic

/-! Actual integrable complex Radon--Nikodym row vectors represent every
kernel integral as evaluation against a vector in one common L1 space. -/
public noncomputable section
open MeasureTheory
namespace LeanShared.RadonNikodymL1Rows
variable {Y : Type*} [MeasurableSpace Y]

/-- The RN row is constructed as an actual L1 vector, not a choice of a
functional representing the kernel. -/
def row (ν μ : Measure Y) [IsFiniteMeasure ν] : Lp ℂ 1 μ :=
  (memLp_one_iff_integrable.mpr
    ((integrableOn_univ.mp (Measure.integrableOn_toReal_rnDeriv
      (μ := ν) (ν := μ) (measure_ne_top _ _))).ofReal)).toLp
      (fun y => ((ν.rnDeriv μ y).toReal : ℂ))

theorem row_ae (ν μ : Measure Y) [IsFiniteMeasure ν] :
    row ν μ =ᵐ[μ] fun y => ((ν.rnDeriv μ y).toReal : ℂ) :=
  MemLp.coeFn_toLp _

theorem integral_mul_row (ν μ : Measure Y) [IsFiniteMeasure ν] [SigmaFinite μ]
    (ac : ν ≪ μ) (f : Y → ℂ) :
    (∫ y, f y * row ν μ y ∂μ) = ∫ y, f y ∂ν := by
  calc
    _ = ∫ y, (ν.rnDeriv μ y).toReal • f y ∂μ := by
      apply integral_congr_ae
      filter_upwards [row_ae ν μ] with y hy
      rw [hy, Complex.real_smul, mul_comm]
    _ = _ := integral_rnDeriv_smul ac

end LeanShared.RadonNikodymL1Rows
