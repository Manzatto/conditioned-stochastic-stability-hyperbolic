module
public import LeanShared.Analysis.ConeFourierPhysicalRowReconstruction
public import LeanShared.Analysis.BTPhysicalTwoNormRows

/-! Weighted physical block rows give the genuine localized-transfer row.
This is the analytic row estimate before taking the completed fake-leaf
supremum; no formal infinite block-matrix identity is assumed. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap ENNReal NNReal BigOperators
namespace LeanShared.ConeFourierWeightedRowBound
open ConeDyadicSymbols BTLinkedDyadicWeights
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm : Set E}

theorem bound (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f output : 𝓢(E,ℂ)) (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (μ : Measure E) (t s loss α upper lower P W strong weak : ℝ)
    (ht : 0 < t) (hs : s < 0) (hLoss : 0 ≤ loss) (gap : t-s+loss < α)
    (hu : 0 < upper) (hl : 0 < lower) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hstrong : 0 ≤ strong) (hweak : 0 ≤ weak)
    (N n : ℕ) (σ : Bool) (row : ℕ → Bool → ℝ≥0)
    (blocks : ∀ l τ, ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
      (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
        ConeFourierBlocks.block (symbols χ Φ (l,τ)) f (G w)‖ₑ ∂μ) ≤ row l τ)
    (linkedBound : ∀ l τ, linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      (row l τ:ℝ) ≤ P*(2:ℝ)^(exponent t s σ*n-exponent t s τ*l)*strong)
    (sharpBound : ∀ l τ, ¬ linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      N ≤ max n l → (row l τ:ℝ) ≤ W*(2:ℝ)^(
        exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))*weak)
    (lowBound : ∀ l τ, ¬ linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      max n l < N → (row l τ:ℝ) ≤ P*(2:ℝ)^(
        exponent t s σ*n-(exponent t s τ-loss)*l)*weak) :
    ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
      (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*f (G w)‖ₑ ∂μ) ≤
    ENNReal.ofReal (P*((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
        max (upper^t) (lower^s))*strong +
      (W*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹)+
        P*(2*((N:ℝ)*(2:ℝ)^((t-s+loss)*N))))*weak) := by
  let ν := ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n)) • μ
  have scaled (v : E → ℂ) : (∫⁻ x,‖v x‖ₑ ∂ν) =
      ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*(∫⁻ x,‖v x‖ₑ ∂μ) := by
    rw [lintegral_smul_measure]; rfl
  rw [← scaled]
  apply ConeFourierPhysicalRowReconstruction.bound χ Φ f output G continuousG
    g continuousg compactg ν (fun l τ => (row l τ:ℝ≥0∞)) _
    (fun l τ => by rw [scaled]; exact blocks l τ)
  intro J
  have scalar := BTPhysicalTwoNormRows.bound t s loss α upper lower P W strong weak
      ht hs hLoss gap hu hl hP hW hstrong hweak N n σ (Finset.range (J+1))
      (fun l τ => (row l τ:ℝ)) linkedBound sharpBound lowBound
  have lift := ENNReal.ofReal_le_ofReal scalar
  have equality : (∑ l ∈ Finset.range (J+1),∑ τ : Bool,(row l τ:ℝ≥0∞)) =
        ENNReal.ofReal (∑ l ∈ Finset.range (J+1),∑ τ : Bool,(row l τ:ℝ)) := by
    norm_cast
    rw [ENNReal.coe_nnreal_eq]
  rw [equality]
  exact lift

end LeanShared.ConeFourierWeightedRowBound
