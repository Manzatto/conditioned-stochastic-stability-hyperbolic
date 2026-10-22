module
public import LeanShared.Analysis.ConeFourierWeightedRowBound

/-! The actual physical block inequalities feed the proved two-norm
reconstruction directly. The finite nonnegative row sequence is constructed
from the three explicit majorants, rather than supplied separately. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap ENNReal NNReal BigOperators
namespace LeanShared.ConeFourierActualTwoNormBound
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
    (hstrong : 0 ≤ strong) (hweak : 0 ≤ weak) (N n : ℕ) (σ : Bool)
    (principal : ∀ l τ,
      ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
          ConeFourierBlocks.block (symbols χ Φ (l,τ)) f (G w)‖ₑ ∂μ) ≤
        ENNReal.ofReal (P*(2:ℝ)^(exponent t s σ*n-exponent t s τ*l)*strong))
    (sharp : ∀ l τ, ¬ linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      N ≤ max n l →
      ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
          ConeFourierBlocks.block (symbols χ Φ (l,τ)) f (G w)‖ₑ ∂μ) ≤
        ENNReal.ofReal (W*(2:ℝ)^(
          exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))*weak))
    (small : ∀ l τ, max n l < N →
      ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
        (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*
          ConeFourierBlocks.block (symbols χ Φ (l,τ)) f (G w)‖ₑ ∂μ) ≤
        ENNReal.ofReal (P*(2:ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l)*weak)) :
    ENNReal.ofReal ((2:ℝ)^(exponent t s σ*n))*
      (∫⁻ x,‖∫ w,FourierSchwartzKernel.kernel output (x-w)*g w*f (G w)‖ₑ ∂μ) ≤
      ENNReal.ofReal (P*((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
        max (upper^t) (lower^s))*strong+
      (W*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹)+
        P*(2*((N:ℝ)*(2:ℝ)^((t-s+loss)*N))))*weak) := by
  classical
  let majorant (l : ℕ) (τ : Bool) : ℝ :=
    if linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) then
      P*(2:ℝ)^(exponent t s σ*n-exponent t s τ*l)*strong
    else if N ≤ max n l then
      W*(2:ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))*weak
    else P*(2:ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l)*weak
  have positive (l : ℕ) (τ : Bool) : 0 ≤ majorant l τ := by
    dsimp [majorant]
    split_ifs <;> positivity
  let row (l : ℕ) (τ : Bool) : ℝ≥0 := ⟨majorant l τ,positive l τ⟩
  apply ConeFourierWeightedRowBound.bound χ Φ f output G continuousG g continuousg compactg
    μ t s loss α upper lower P W strong weak ht hs hLoss gap hu hl hP hW hstrong hweak N n σ row
  · intro l τ
    rw [ENNReal.coe_nnreal_eq]
    change _ ≤ ENNReal.ofReal (majorant l τ)
    by_cases linkedPair : linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ)
    · simpa only [majorant,ite_eq_left linkedPair] using principal l τ
    · by_cases high : N ≤ max n l
      · simpa only [majorant,ite_eq_right linkedPair,ite_eq_left high] using sharp l τ linkedPair high
      · simpa only [majorant,ite_eq_right linkedPair,ite_eq_right high] using small l τ (Nat.lt_of_not_ge high)
  · intro l τ linkedPair
    exact (show majorant l τ = _ from ite_eq_left linkedPair).le
  · intro l τ linkedPair high
    exact (show majorant l τ = _ by simp only [majorant,ite_eq_right linkedPair,ite_eq_left high]).le
  · intro l τ linkedPair low
    exact (show majorant l τ = _ by
      simp only [majorant,ite_eq_right linkedPair,ite_eq_right (Nat.not_le.mpr low)]).le

end LeanShared.ConeFourierActualTwoNormBound
