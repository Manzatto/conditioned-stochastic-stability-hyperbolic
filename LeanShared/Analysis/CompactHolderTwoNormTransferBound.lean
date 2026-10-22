module
public import LeanShared.Analysis.CompactHolderPhysicalBlocks
public import LeanShared.Analysis.ConeFourierActualTwoNormBound

/-! The actual physical principal, nonlinked and finite-square bounds
control the completed ordinary realization. Fourier reconstruction and both
native frequency/leaf suprema are proved operations, not extra hypotheses. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal
namespace LeanShared.CompactHolderTwoNormTransferBound
open ConeDyadicSymbols BTLinkedDyadicWeights
variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  {Cp Cm Dp Dm : Set E}

theorem norm_bound
    (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
    (leaves : A → GraphLeafNorm.GraphLeaf U E J)
    (inputRadial outputRadial : RadialCutoff)
    (inputAngle : AngularCutoff Cp Cm) (outputAngle : AngularCutoff Dp Dm)
    {S : Set E} (compact : IsCompact S) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (f : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (output : EuclideanSmoothHolderCore.space compact.closure hb hb1)
    (represented : ∀ x, EuclideanSmoothHolderCore.physical compact.closure hb hb1 output x =
      g x*f (G x))
    (t s loss α upper lower P W strong weak : ℝ)
    (ht : 0 < t) (hs : s < 0) (hLoss : 0 ≤ loss) (gap : t-s+loss < α)
    (hu : 0 < upper) (hl : 0 < lower) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hstrong : 0 ≤ strong) (hweak : 0 ≤ weak) (N : ℕ)
    (margin : ∀ sign, exponent t s sign ≤ b)
    (principal : ∀ (j : ℕ × Bool) a l τ,
      ENNReal.ofReal ((2:ℝ)^(exponent t s j.2*j.1))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w)*g w*
          ConeFourierBlocks.block (symbols inputRadial inputAngle (l,τ)) f (G w)‖ₑ ∂(leaves a).measure μ) ≤
        ENNReal.ofReal (P*(2:ℝ)^(exponent t s j.2*j.1-exponent t s τ*l)*strong))
    (sharp : ∀ (j : ℕ × Bool) a l τ,
      ¬ linked (plusThreshold upper) (minusThreshold lower) j (l,τ) → N ≤ max j.1 l →
      ENNReal.ofReal ((2:ℝ)^(exponent t s j.2*j.1))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w)*g w*
          ConeFourierBlocks.block (symbols inputRadial inputAngle (l,τ)) f (G w)‖ₑ ∂(leaves a).measure μ) ≤
        ENNReal.ofReal (W*(2:ℝ)^(
          exponent t s j.2*j.1-(exponent t s τ-loss)*l-α*(max j.1 l:ℕ))*weak))
    (small : ∀ (j : ℕ × Bool) a l τ, max j.1 l < N →
      ENNReal.ofReal ((2:ℝ)^(exponent t s j.2*j.1))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w)*g w*
          ConeFourierBlocks.block (symbols inputRadial inputAngle (l,τ)) f (G w)‖ₑ ∂(leaves a).measure μ) ≤
        ENNReal.ofReal (P*(2:ℝ)^(exponent t s j.2*j.1-(exponent t s τ-loss)*l)*weak)) :
    ‖CompactHolderPhysicalBlocks.realize μ hJ leaves outputRadial outputAngle compact hb hb1
      (exponent t s) margin output‖ ≤
      P*((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
        max (upper^t) (lower^s))*strong+
      (W*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹)+
        P*(2*((N:ℝ)*(2:ℝ)^((t-s+loss)*N))))*weak := by
  have positiveRows : 0 ≤ rowConstant t s := (rowConstant_positive t s ht hs).le
  have decay : (2:ℝ)^(-(α-(t-s+loss))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have denominator : 0 ≤ (1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr decay).le
  apply CompactHolderPhysicalBlocks.norm_le_of_rows μ hJ leaves outputRadial outputAngle
    compact hb hb1 (exponent t s) margin output _ (by positivity)
  intro j a
  have row := ConeFourierActualTwoNormBound.bound inputRadial inputAngle f
    (symbols outputRadial outputAngle j) G continuousG g continuousg compactg
    ((leaves a).measure μ) t s loss α upper lower P W strong weak
    ht hs hLoss gap hu hl hP hW hstrong hweak N j.1 j.2
    (principal j a) (sharp j a) (small j a)
  simpa only [represented,mul_assoc] using row

end LeanShared.CompactHolderTwoNormTransferBound
