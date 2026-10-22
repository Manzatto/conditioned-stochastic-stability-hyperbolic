module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafPhysicalKernelRow
public import LeanShared.Analysis.ActualDyadicTwoKernelBound
public import LeanShared.Analysis.PhysicalEnvelopeKernelMajorant
public import LeanShared.Analysis.ScaledEnvelopeMass

/-! Sharp fractional nonlinked decay for the literal physical dyadic kernel
on the entire induced-volume fake-leaf family. Spatial dilation masses and
all frequency-volume factors cancel in the proved operator estimate. -/
public noncomputable section
set_option maxHeartbeats 2000000
open Set MeasureTheory
open scoped SchwartzMap ContDiff ENNReal NNReal BoundedContinuousFunction Pointwise
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared HilbertFrequencyPair NormalizedDyadicKernel DyadicFrequencyScale
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem dyadic_kernel_leaf_bound {P ι S R : Type*}
    [Fintype ι] [Fintype S] [Fintype R] (basis : OrthonormalBasis ι ℝ E)
    (U : Submodule ℝ E) {sourceC targetC : Set E}
    (sourceCone : ConeData U sourceC) (targetCone : ConeData U targetC)
    (μ : Measure U) [μ.IsAddHaarMeasure]
    (ambient : Measure E) [ambient.IsAddHaarMeasure]
    (ρ : ℝ) (hρ : 0 < ρ) {δ α D H G₀ G₁ K : ℝ}
    (positive : 0 < δ) (hα : 0 < α) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hG₀ : 0 ≤ G₀) (hG₁ : 0 ≤ G₁) (hK : 0 ≤ K)
    (G : P → E → E) (smoothG : ∀ p, ContDiff ℝ 1 (G p))
    (value : ∀ p w, ‖fderiv ℝ (G p) w‖ ≤ D)
    (holder : ∀ p x y, ‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖ ≤ H*dist x y^α)
    (low high : S → 𝓢(E,ℂ)) (low' high' : R → 𝓢(E,ℂ))
    (cl : ∀ i, HasCompactSupport (low i)) (ch : ∀ i, HasCompactSupport (high i))
    (cl' : ∀ j, HasCompactSupport (low' j)) (ch' : ∀ j, HasCompactSupport (high' j))
    (g : P → E →ᵇℂ) {L₀ : Set E} (compactL₀ : IsCompact L₀)
    (supported : ∀ p, tsupport (fun w => g p w) ⊆ L₀)
    (gvalue : ∀ p w, ‖g p w‖ ≤ G₀)
    (gholder : ∀ p x y, ‖g p x-g p y‖ ≤ G₁*dist x y^α)
    (good : P → (ℕ × S) → (ℕ × R) → Prop)
    (gap : ∀ p j k, good p j k → ∀ w ξ η, g p w ≠ 0 →
      DyadicSymbols.symbol low high j (((2:ℝ)^j.1) • ξ) ≠ 0 →
      DyadicSymbols.symbol low' high' k (((2:ℝ)^k.1) • η) ≠ 0 →
      δ ≤ ‖SmoothNonstationarySymbol.gradient (fderiv ℝ (G p) w,
        (leftRatio j.1 k.1 • ξ,rightRatio j.1 k.1 • η))‖^2)
    (F : P → OpenPartialHomeomorph E E)
    (forward : ∀ p, ContDiffOn ℝ 1 (F p) (F p).source)
    (backward : ∀ p, ContDiffOn ℝ 1 (F p).symm (F p).target)
    (measurableF : ∀ p, Measurable (F p))
    (O : Set E) (openO : IsOpen O) (inside : ∀ p, O ⊆ (F p).source)
    (safe : L₀+Metric.closedBall (0:E) ρ ⊆ O)
    (same : ∀ p, EqOn (G p) (F p) (L₀+Metric.closedBall (0:E) ρ))
    (images : ∀ p, ∀ Γ : Index U sourceC, Γ.val ⊆ O →
      ∃ image : Index U targetC, image.val = (F p) '' Γ.val)
    (inverse : ∀ p x, x ∈ O → ‖fderiv ℝ (F p).symm (F p x)‖ ≤ K) :
    ∃ C : ℝ≥0, ∀ p j k, good p j k → ∀ (u : E → ℂ), Measurable u → ∀ B : ℝ≥0∞,
      (∀ Δ : Index U targetC,
        ∫⁻ y, ‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B) →
      ∀ Γ : Index U sourceC,
      (∫⁻ x, ‖∫ y, (∫ w, g p w*DyadicSymbols.kernel low high j (x-w)*
        DyadicSymbols.kernel low' high' k (G p w-y) ∂ambient)*u y ∂ambient‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤
        (C : ℝ≥0∞)*ENNReal.ofReal ((2:ℝ)^(-α*(max j.1 k.1:ℕ)))*B := by
  let m := Module.finrank ℝ E+1
  let q : ℝ := (2*Real.pi)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  let mass : ℝ := (q^(Module.finrank ℝ E))⁻¹*
    (∫ x, envelope m (x:E) ∂ambient)
  have nonnegativeMass : 0 ≤ mass := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro x
    dsimp [envelope]
    positivity
  let cost := GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ E)) K
  have nonnegativeCost : 0 ≤ cost := GraphJacobian.densityBound_nonneg K
  obtain ⟨c,hc,physical⟩ := ActualDyadicTwoKernelBound.exists_bound basis ambient m ρ hρ positive
    hα hD hH hG₀ hG₁ G smoothG value holder low high low' high' cl ch cl' ch'
    g compactL₀ supported gvalue gholder good gap
  let total : ℝ≥0 := ⟨c*(mass*(cost*mass)), by positivity⟩
  have totalEq : (total : ℝ≥0∞) = ENNReal.ofReal (c*(mass*(cost*mass))) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  refine ⟨total, ?_⟩
  intro p j k accepted u mu B leafBound Γ
  let a : ℝ := (2:ℝ)^j.1
  let b : ℝ := (2:ℝ)^k.1
  let decay : ℝ := (2:ℝ)^(-α*(max j.1 k.1:ℕ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 ≤ decay := by dsimp [decay]; positivity
  let k₀ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (a^(Module.finrank ℝ E)*envelope m ((q*a) • x))
  let k₁ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (b^(Module.finrank ℝ E)*envelope m ((q*b) • x))
  have envContinuous : Continuous (envelope m : E → ℝ) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    positivity
  have mk₀ : Measurable k₀ :=
    (continuous_const.mul (envContinuous.comp (continuous_const.smul continuous_id))).measurable.ennreal_ofReal
  have mk₁ : Measurable k₁ :=
    (continuous_const.mul (envContinuous.comp (continuous_const.smul continuous_id))).measurable.ennreal_ofReal
  have mass₀ : (∫⁻ z,k₀ z ∂ambient) = ENNReal.ofReal mass := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (q^(Module.finrank ℝ E))⁻¹)]
    exact ScaledEnvelopeMass.lintegral_scaled_frequency ambient (by dsimp [m]; omega) ha hq
  have mass₁ : (∫⁻ z,k₁ z ∂ambient) = ENNReal.ofReal mass := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (q^(Module.finrank ℝ E))⁻¹)]
    exact ScaledEnvelopeMass.lintegral_scaled_frequency ambient (by dsimp [m]; omega) hb hq
  let kernel : E → E → ℂ := fun x y => ∫ w, g p w*DyadicSymbols.kernel low high j (x-w)*
    DyadicSymbols.kernel low' high' k (G p w-y) ∂ambient
  let coefficient : ℝ≥0 := ⟨c*decay,mul_nonneg hc hd⟩
  have majorant (x y : E) : ‖kernel x y‖ₑ ≤ (coefficient : ℝ≥0∞)*
      (∫⁻ w,k₀ (x-w)*O.indicator (fun _ => 1) w*k₁ (F p w-y) ∂ambient) := by
    rw [ENNReal.coe_nnreal_eq]
    exact PhysicalEnvelopeKernelMajorant.bound ambient m ha.le hb.le (mul_nonneg hc hd)
      (G p) (F p) (smoothG p).continuous
      (compactL₀.add (isCompact_closedBall 0 ρ)) safe (same p) kernel x y (physical p j k accepted x y)
  have bound := physical_kernel_row_bound U sourceCone targetCone μ ambient (F p) (forward p)
    (backward p) (measurableF p) O openO (inside p) (images p) hK (inverse p)
    k₀ k₁ mk₀ mk₁ u mu kernel coefficient majorant B leafBound Γ
  rw [mass₀,mass₁] at bound
  refine bound.trans_eq ?_
  rw [totalEq, ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal (c*decay)*(ENNReal.ofReal mass*(ENNReal.ofReal cost*(ENNReal.ofReal mass*B))) =
    ENNReal.ofReal (c*(mass*(cost*mass)))*ENNReal.ofReal decay*B
  simp only [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul nonnegativeMass,
    ENNReal.ofReal_mul nonnegativeCost]
  ring

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
