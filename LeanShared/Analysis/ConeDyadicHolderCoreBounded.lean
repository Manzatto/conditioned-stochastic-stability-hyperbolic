module
public import LeanShared.Analysis.DyadicHolderCoreBounded
public import LeanShared.Analysis.ConeDyadicSymbols

/-! Smooth-core boundedness for the literal manuscript cone symbols is
proved from the actual Fourier/leaf estimates. No dyadic boundedness source
is supplied for the small positive/negative exponent models. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace LeanShared.ConeDyadicHolderCoreBounded
open ConeDyadicSymbols
variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
  {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1 : a<1)
  (t : Bool → ℝ) (margin : ∀s,t s≤a)

include compact ha ha1 margin in
theorem smoothCoreBounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K (symbols χ Φ) t := by
  let lowBase : Bool → 𝓢(E,ℂ) := fun _ => FourierSchwartzKernel.symbol
    (low χ) (low_hasCompactSupport χ) (low_smooth χ)
  let highBase : Bool → 𝓢(E,ℂ) := fun s => FourierSchwartzKernel.symbol
    (high χ Φ.toFun s) (high_hasCompactSupport χ Φ.toFun s) (high_smooth χ Φ s)
  have zero (s : Bool) : highBase s 0=0 := by
    change (high χ Φ.toFun s) 0=0
    rw [high, highReal, annular_zero_near_origin χ (by simp), mul_zero, Complex.ofReal_zero]
  exact DyadicHolderCoreBounded.smoothCoreBounded μ hJ leaves lowBase highBase zero compact ha ha1 t margin
end LeanShared.ConeDyadicHolderCoreBounded
