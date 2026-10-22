module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeInputBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafDyadicKernelBound
public import LeanShared.Analysis.BoundedFamilyBTPhaseGap
public import LeanShared.Analysis.ActualInputBlockKernelIdentity
public import LeanShared.Analysis.HomeomorphDerivativeEquivalence
import all LeanShared.Analysis.DyadicSymbols
import all LeanShared.Analysis.ConeDyadicSymbols

/-! Actual nonlinked physical rows for the full native input norm. The phase
gap is produced from bounded actual derivative matrices and a closed cone
margin, without a topology on the parameter set. Actual inverse derivatives
give coercivity; enlarged symbols and Fubini identify the literal input block. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared ConeDyadicSymbols BTLinkedDyadicWeights DyadicFrequencyScale

private theorem adjoint_coercive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E ≃ₜ E) (smooth : Differentiable ℝ H) (inverseSmooth : Differentiable ℝ H.symm)
    {K : ℝ} (hK : 0 ≤ K) (inverse : ∀ x, ‖fderiv ℝ H.symm x‖ ≤ K) (x v : E) :
    (K+1)⁻¹ * ‖v‖ ≤ ‖(fderiv ℝ H x).adjoint v‖ := by
  have identity := congrArg (fun A : E →L[ℝ] E => A.adjoint)
    (HomeomorphDerivativeEquivalence.comp_inverse H smooth inverseSmooth x)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at identity
  have undo : (fderiv ℝ H.symm (H x)).adjoint ((fderiv ℝ H x).adjoint v) = v :=
    congrArg (fun A : E →L[ℝ] E => A v) identity
  have normBound := (fderiv ℝ H.symm (H x)).adjoint.le_opNorm ((fderiv ℝ H x).adjoint v)
  rw [undo, ContinuousLinearMap.adjoint.norm_map] at normBound
  have bound : ‖v‖ ≤ (K+1) * ‖(fderiv ℝ H x).adjoint v‖ :=
    normBound.trans (mul_le_mul_of_nonneg_right ((inverse (H x)).trans (by linarith)) (norm_nonneg _))
  have divide : ‖v‖/(K+1) ≤ ‖(fderiv ℝ H x).adjoint v‖ :=
    (div_le_iff₀ (show 0 < K+1 by linarith)).mpr (by simpa only [mul_comm] using bound)
  simpa only [div_eq_mul_inv, mul_comm] using divide

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {P I ι κ : Type*} [Finite I] [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem exists_global_nonlinked_block_bound
    (ambientBasis : OrthonormalBasis κ ℝ E)
    (planes : I → Submodule ℝ E) (plus : I → Set E)
    (cone : ∀ i, ConeData (planes i) (plus i))
    (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
    (basis : ∀ i, OrthonormalBasis ι ℝ (planes i)) (i : I)
    {Dp Dm Cm narrow : Set E} (sourceCone : ConeData (planes i) Dp)
    (H : P → E ≃ₜ E) (smooth : ∀ p, ContDiff ℝ 1 (H p))
    (inverseSmooth : ∀ p, ContDiff ℝ 1 (H p).symm)
    {α D L G₀ G₁ K upper lower : ℝ}
    (hα : 0 < α) (hD : 0 ≤ D) (hL : 0 ≤ L) (hG₀ : 0 ≤ G₀) (hG₁ : 0 ≤ G₁) (hK : 0 ≤ K)
    (value : ∀ p x, ‖fderiv ℝ (H p) x‖ ≤ D)
    (holder : ∀ p x y, ‖fderiv ℝ (H p) x-fderiv ℝ (H p) y‖ ≤ L*dist x y^α)
    (inverse : ∀ p x, ‖fderiv ℝ (H p).symm x‖ ≤ K)
    (closedNarrow : IsClosed narrow) (margin : ∀ v ∈ narrow, v ≠ 0 → v ∈ interior Dm)
    (sourceScale : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ plus i, c • v ∈ plus i)
    (targetScale : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ Dm, c • v ∈ Dm)
    (action : ∀ p x v, v ≠ 0 → v ∉ interior (plus i) → (fderiv ℝ (H p) x).adjoint v ∈ narrow)
    (hu : 0 < upper) (hl : 0 < lower)
    (upperBound : ∀ p x v, (fderiv ℝ (H p) x).adjoint v ∉ narrow →
      ‖(fderiv ℝ (H p) x).adjoint v‖ ≤ upper*‖v‖)
    (lowerBound : ∀ p x v, v ∉ interior (plus i) → lower*‖v‖ ≤ ‖(fderiv ℝ (H p) x).adjoint v‖)
    (outputRadial inputRadial : RadialCutoff) (outputAngle : AngularCutoff Dp Dm)
    (inputCutoffs : ConstructedEnlargedConeSymbols.Cutoffs (plus i) Cm)
    (g : P → E →ᵇ ℂ) {L₀ : Set E} (compactL₀ : IsCompact L₀)
    (supported : ∀ p, tsupport (fun w => g p w) ⊆ L₀)
    (gvalue : ∀ p w, ‖g p w‖ ≤ G₀)
    (gholder : ∀ p x y, ‖g p x-g p y‖ ≤ G₁*dist x y^α)
    (images : ∀ p, ∀ Γ : Index (planes i) Dp,
      ∃ image : Index (planes i) (plus i), image.val = (H p) '' Γ.val)
    {S : Set E} (compactS : IsCompact S) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (t : Bool → ℝ) (tBound : ∀ sign, t sign ≤ b) :
    ∃ N : ℕ, ∃ C : ℝ≥0, ∀ p (j k : ℕ × Bool), N < max j.1 k.1 →
      ¬ linked (plusThreshold upper) (minusThreshold lower) j k →
      ∀ f : SchwartzJetSpace.supportedCore S, ∀ Γ : Index (planes i) Dp,
      (∫⁻ x, ‖∫ w, FourierSchwartzKernel.kernel (symbols outputRadial outputAngle j) (x-w) *
        g p w * ConeFourierBlocks.block (symbols inputRadial inputCutoffs.original k) f.val (H p w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)^(-α*(max j.1 k.1 : ℕ))) *
          (ENNReal.ofReal ((2 : ℝ)^(-(t k.2 * k.1))) *
            ENNReal.ofReal ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
              inputRadial inputCutoffs.original compactS hb hb1 t tBound i f‖) := by
  have differentiable (p : P) : Differentiable ℝ (H p) := (smooth p).differentiable (by norm_num)
  have inverseDifferentiable (p : P) : Differentiable ℝ (H p).symm :=
    (inverseSmooth p).differentiable (by norm_num)
  let A : P × E → E →L[ℝ] E := fun z => (fderiv ℝ (H z.1) z.2).adjoint
  have normA (z : P × E) : ‖A z‖ ≤ D := by
    change ‖(fderiv ℝ (H z.1) z.2).adjoint‖ ≤ D
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact value z.1 z.2
  have coercivity (z : P × E) (v : E) : (K+1)⁻¹ * ‖v‖ ≤ ‖A z v‖ :=
    adjoint_coercive (H z.1) (differentiable z.1) (inverseDifferentiable z.1) hK (inverse z.1) z.2 v
  obtain ⟨δ, positiveδ, N, phase⟩ := BoundedFamilyBTPhaseGap.exists_gap A D (K+1)⁻¹ upper lower
    normA (by positivity) coercivity closedNarrow margin sourceScale targetScale
    (fun z => action z.1 z.2) hu hl (fun z => upperBound z.1 z.2) (fun z => lowerBound z.1 z.2)
    outputRadial inputRadial outputAngle inputCutoffs
  let good (_p : P) (j k : ℕ × Bool) : Prop :=
    N < max j.1 k.1 ∧ ¬ linked (plusThreshold upper) (minusThreshold lower) j k
  have gap : ∀ p j k, good p j k → ∀ w ξ η, g p w ≠ 0 →
      DyadicSymbols.symbol (ConeHolderAnisotropicEmbedding.lowBase outputRadial)
        (ConeHolderAnisotropicEmbedding.highBase outputRadial outputAngle) j (((2:ℝ)^j.1) • ξ) ≠ 0 →
      DyadicSymbols.symbol (fun _ : Bool => EnlargedConeDyadicSymbols.low inputRadial)
        (fun sign => EnlargedConeDyadicSymbols.high inputRadial (inputCutoffs.enlarged sign)
          (inputCutoffs.smooth sign)) k (((2:ℝ)^k.1) • η) ≠ 0 →
      δ ≤ ‖SmoothNonstationarySymbol.gradient (fderiv ℝ (H p) w,
        (leftRatio j.1 k.1 • ξ, rightRatio j.1 k.1 • η))‖^2 := by
    intro p j k accepted w ξ η _ output input
    have bound := phase (p,w) j.1 k.1 j.2 k.2 accepted.1 accepted.2 ξ η output input
    simpa only [SmoothNonstationarySymbol.gradient, A, norm_sub_rev] using bound
  obtain ⟨C, rows⟩ := dyadic_kernel_leaf_bound ambientBasis (planes i) sourceCone (cone i)
    volume volume 1 (by norm_num) positiveδ hα hD hL hG₀ hG₁ hK
    (fun p => (H p : E → E)) smooth value holder
    (ConeHolderAnisotropicEmbedding.lowBase outputRadial)
    (ConeHolderAnisotropicEmbedding.highBase outputRadial outputAngle)
    (fun _ : Bool => EnlargedConeDyadicSymbols.low inputRadial)
    (fun sign => EnlargedConeDyadicSymbols.high inputRadial (inputCutoffs.enlarged sign) (inputCutoffs.smooth sign))
    (by intro sign; exact low_hasCompactSupport outputRadial)
    (by intro sign; exact high_hasCompactSupport outputRadial outputAngle.toFun sign)
    (fun _ => EnlargedConeDyadicSymbols.low_compact inputRadial)
    (fun sign => EnlargedConeDyadicSymbols.high_compact inputRadial (inputCutoffs.enlarged sign) (inputCutoffs.smooth sign))
    g compactL₀ supported gvalue gholder good gap
    (fun p => (H p).toOpenPartialHomeomorph)
    (fun p => (smooth p).contDiffOn) (fun p => (inverseSmooth p).contDiffOn)
    (fun p => (H p).continuous.measurable) univ isOpen_univ (fun _ => subset_rfl)
    (subset_univ _) (fun _ _ _ => rfl) (fun p Γ _ => images p Γ)
    (fun p x _ => inverse p (H p x))
  refine ⟨N, C, ?_⟩
  intro p j k large nonlinked f Γ
  have bound := rows p j k ⟨large, nonlinked⟩
    (ConeFourierBlocks.block (symbols inputRadial inputCutoffs.original k) f.val)
    (ConeFourierBlocks.block _ f.val).continuous.measurable _
    (AllFakeLeafHolderCoreBounds.input_leaf_bound planes plus cone coordinates basis inputRadial
      inputCutoffs.original compactS hb hb1 t tBound i f k) Γ
  have physical (x : E) := ActualInputBlockKernelIdentity.identity
    (symbols outputRadial outputAngle j) (symbols inputRadial inputCutoffs.original k)
    (EnlargedConeDyadicSymbols.symbols inputRadial inputCutoffs.enlarged inputCutoffs.smooth k)
    (inputCutoffs.multiplier_identity inputRadial k) (H p) (H p).continuous (g p)
    (g p).continuous (compactL₀.of_isClosed_subset (isClosed_tsupport _) (supported p)) f.val x
  have output_symbol : DyadicSymbols.symbol (ConeHolderAnisotropicEmbedding.lowBase outputRadial)
      (ConeHolderAnisotropicEmbedding.highBase outputRadial outputAngle) j =
      symbols outputRadial outputAngle j := rfl
  simp_rw [physical]
  simpa only [DyadicSymbols.kernel, output_symbol,
    EnlargedConeDyadicSymbols.symbols] using bound

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
