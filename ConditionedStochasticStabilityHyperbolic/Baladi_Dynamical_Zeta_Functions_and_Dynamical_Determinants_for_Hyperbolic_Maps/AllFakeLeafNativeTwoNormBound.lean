module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafPrincipalBlockRows
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeLeafMeasure
public import LeanShared.Analysis.CompactHolderTwoNormTransferBound

/-! Compose raw physical leaf estimates with the actual heterogeneous
native norms. The finite-square estimate is obtained by applying the same
principal operator bound to the weaker input blocks. The two frequency
and full fake-leaf suprema are retained by the completed realization.
This is the analytic consumer of the separately constructed physical row
producers, not a new row-source interface. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
open LeanShared AllFakeLeafModel ConeDyadicSymbols BTLinkedDyadicWeights
variable {E I ι : Type*} [Finite I] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i))

theorem native_two_norm_bound
    (i o : I) (planeSame : planes i = planes o) (plusSame : plus i = plus o)
    {inputPlus inputMinus outputPlus outputMinus : Set E}
    (inputRadial outputRadial : RadialCutoff)
    (inputAngle : AngularCutoff inputPlus inputMinus)
    (outputAngle : AngularCutoff outputPlus outputMinus)
    {inputSupport outputSupport : Set E}
    (compactInput : IsCompact inputSupport) (compactOutput : IsCompact outputSupport)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (f : SchwartzJetSpace.supportedCore inputSupport)
    (G : E → E) (continuousG : Continuous G)
    (g : E → ℂ) (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (output : EuclideanSmoothHolderCore.space compactOutput.closure hb hb1)
    (represented : ∀ x, EuclideanSmoothHolderCore.physical compactOutput.closure hb hb1 output x =
      g x * f.val (G x))
    (t s loss α upper lower : ℝ)
    (ht : 0 < t) (hs : s < 0) (hLoss : 0 ≤ loss) (gap : t-s+loss < α)
    (hu : 0 < upper) (hl : 0 < lower) (A cost W : ℝ≥0) (cutoff : ℕ)
    (margin : ∀ sign, exponent t s sign ≤ b)
    (principal : ∀ (j k : ℕ × Bool) (Γ : Index (planes o) (plus o)) (B : ℝ≥0∞),
      (∀ Δ : Index (planes o) (plus o),
        (∫⁻ x, ‖ConeFourierBlocks.block (symbols inputRadial inputAngle k) f.val x‖ₑ
          ∂EmbeddedSubmanifoldVolume.volume (planes o) volume Δ.val) ≤ B) →
      (∫⁻ x, ‖∫ w, FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w) *
        g w * ConeFourierBlocks.block (symbols inputRadial inputAngle k) f.val (G w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume (planes o) volume Γ.val) ≤
      (A : ℝ≥0∞) * ((cost : ℝ≥0∞) * B))
    (nonlinked : ∀ (j k : ℕ × Bool) (Γ : Index (planes o) (plus o)),
      cutoff < max j.1 k.1 → ¬ linked (plusThreshold upper) (minusThreshold lower) j k →
      (∫⁻ x, ‖∫ w, FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w) *
        g w * ConeFourierBlocks.block (symbols inputRadial inputAngle k) f.val (G w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume (planes o) volume Γ.val) ≤
      (W : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)^(-α*(max j.1 k.1:ℕ))) *
        (ENNReal.ofReal ((2 : ℝ)^(-((exponent t s k.2-loss)*k.1))) *
          ENNReal.ofReal ‖coreBlocks planes plus cone coordinates basis inputRadial inputAngle
            compactInput hb hb1 (fun sign => exponent t s sign-loss)
            (fun sign => (sub_le_self _ hLoss).trans (margin sign)) i f‖)) :
    let strong := ‖coreBlocks planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (exponent t s) margin i f‖
    let weak := ‖coreBlocks planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (fun sign => exponent t s sign-loss)
      (fun sign => (sub_le_self _ hLoss).trans (margin sign)) i f‖
    ‖CompactHolderPhysicalBlocks.realize (volume : Measure (EuclideanSpace ℝ ι))
      (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
      (leaves planes plus cone coordinates basis o) outputRadial outputAngle compactOutput hb hb1
      (exponent t s) margin output‖ ≤
      ((A * cost : ℝ≥0) : ℝ) *
        ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*max (upper^t) (lower^s))*strong +
      ((W : ℝ)*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹) +
        ((A * cost : ℝ≥0) : ℝ)*(2*(((cutoff+1:ℕ):ℝ)*(2:ℝ)^((t-s+loss)*(((cutoff+1:ℕ):ℝ))))))*weak := by
  dsimp only
  apply CompactHolderTwoNormTransferBound.norm_bound
    (volume : Measure (EuclideanSpace ℝ ι))
    (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
    (leaves planes plus cone coordinates basis o) inputRadial outputRadial inputAngle outputAngle
    compactOutput hb hb1 f.val G continuousG g continuousg compactg output represented
    t s loss α upper lower ((A*cost : ℝ≥0) : ℝ) (W : ℝ)
    ‖coreBlocks planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (exponent t s) margin i f‖
    ‖coreBlocks planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (fun sign => exponent t s sign-loss)
      (fun sign => (sub_le_self _ hLoss).trans (margin sign)) i f‖
    ht hs hLoss gap hu hl (A*cost).coe_nonneg W.coe_nonneg (norm_nonneg _) (norm_nonneg _)
    (cutoff+1) margin
  · intro j a l τ
    rw [native_leaf_measure]
    exact weighted_principal_block_row planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (exponent t s) margin i (planes o) (plus o) planeSame plusSame f (l,τ)
      A cost _ (exponent t s j.2*j.1) (fun B bound => principal j (l,τ) (a o) B bound)
  · intro j a l τ unlinked large
    rw [native_leaf_measure]
    apply DyadicPhysicalRowWeight.decay W (exponent t s j.2*j.1)
      ((exponent t s τ-loss)*l) (α*(max j.1 l:ℕ)) _
    simpa only [neg_mul] using
      nonlinked j (l,τ) (a o) (lt_of_lt_of_le (Nat.lt_succ_self cutoff) large) unlinked
  · intro j a l τ _
    rw [native_leaf_measure]
    exact weighted_principal_block_row planes plus cone coordinates basis inputRadial inputAngle
      compactInput hb hb1 (fun sign => exponent t s sign-loss)
      (fun sign => (sub_le_self _ hLoss).trans (margin sign))
      i (planes o) (plus o) planeSame plusSame f (l,τ) A cost _ (exponent t s j.2*j.1)
      (fun B bound => principal j (l,τ) (a o) B bound)

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafHolderCoreBounds
