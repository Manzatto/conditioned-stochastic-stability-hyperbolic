module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application

/-! The derived HG2 families do not depend on the normalizer of the weighted chain. If every killed
kernel of one chain family is a fixed positive multiple of the other, every restricted transfer
operator is that multiple of the other one; rank-one data rescale with the same mean and
eigenvector, so the product measures, supports and all remaining fields are unchanged. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.FamiliesRescale
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth FiltrationPressureConfinement ComplexStrongFeller RestrictedLayerChain
open LayerQuasiErgodic DerivedHG2Application KellerLiverani1999

section RankOne
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rank-one spectral data of a positive multiple of an operator. -/
def rankOneRescale {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one) (c : ℝ) (hc : 0 < c) :
    RankOneSpectralData (c • P) one where
  rate := c * d.rate
  rate_pos := mul_pos hc d.rate_pos
  mean := d.mean
  eigenvector := d.eigenvector
  mean_eigenvector := d.mean_eigenvector
  mean_one_pos := d.mean_one_pos
  right_eigenvector := by
    rw [smul_apply, d.right_eigenvector, smul_smul]
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    intro n
    have same : (c * d.rate)⁻¹ • (c • P) = d.rate⁻¹ • P := by
      rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
    rw [same]
    exact d.power_gap n

/-- Rank-one spectral data transported along an equality of operators, with the same fields. -/
def rankOneCongr {P Q : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one) (h : P = Q) :
    RankOneSpectralData Q one :=
  { d with
    right_eigenvector := h ▸ d.right_eigenvector
    power_gap := h ▸ d.power_gap }

@[simp] theorem rankOneRescale_mean {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)
    (c : ℝ) (hc : 0 < c) : (rankOneRescale d c hc).mean = d.mean := rfl

@[simp] theorem rankOneRescale_eigenvector {P : E →L[ℝ] E} {one : E}
    (d : RankOneSpectralData P one) (c : ℝ) (hc : 0 < c) :
    (rankOneRescale d c hc).eigenvector = d.eigenvector := rfl

@[simp] theorem rankOneCongr_mean {P Q : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)
    (h : P = Q) : (rankOneCongr d h).mean = d.mean := rfl

@[simp] theorem rankOneCongr_eigenvector {P Q : E →L[ℝ] E} {one : E}
    (d : RankOneSpectralData P one) (h : P = Q) : (rankOneCongr d h).eigenvector = d.eigenvector :=
  rfl

end RankOne

variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- Restricted transfer operators of proportional killed kernels are proportional. -/
theorem restricted_transfer_scale (C₁ C₂ : CanonicalChain X) (c : ℝ) (hc : 0 < c)
    (scale : ∀ x, C₂.killedTransition x = ENNReal.ofReal c • C₁.killedTransition x)
    (U : Set X) (hU : MeasurableSet U) [CompactSpace U]
    (sf₁ : HasStrongFellerKernel (chain C₁ U hU)) (sf₂ : HasStrongFellerKernel (chain C₂ U hU)) :
    transferOperator (𝕜 := ℝ) (chain C₂ U hU) sf₂ =
      c • transferOperator (𝕜 := ℝ) (chain C₁ U hU) sf₁ := by
  ext f x
  rw [smul_apply, BoundedContinuousFunction.smul_apply, transferOperator_apply,
    transferOperator_apply, RestrictedLayerChain.killedTransition,
    RestrictedLayerChain.killedTransition, SubtypeKernel.restrict_apply,
    SubtypeKernel.restrict_apply, scale, Measure.comap_smul, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul]

omit [CompactSpace X] in
/-- Product measures only depend on the mean functional and the eigenvector of the rank-one data. -/
theorem productMeasure_congr (C₁ C₂ : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
    [CompactSpace U]
    (sf₁ : HasStrongFellerKernel (chain C₁ U hU)) (sf₂ : HasStrongFellerKernel (chain C₂ U hU))
    (d₁ : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C₁ U hU) sf₁) (1 : U →ᵇ ℝ))
    (d₂ : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C₂ U hU) sf₂) (1 : U →ᵇ ℝ))
    (hm : d₂.mean = d₁.mean) (hv : d₂.eigenvector = d₁.eigenvector) :
    productMeasure (chain C₂ U hU) sf₂ d₂ = productMeasure (chain C₁ U hU) sf₁ d₁ := by
  unfold productMeasure leadingMeasure RankOneSpectralData.eigenmeasure
  have key : ∀ (L₁ L₂ : (U →ᵇ ℝ) →L[ℝ] ℝ) (h₁ : ∀ f : U →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L₁ f)
      (h₂ : ∀ f : U →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ L₂ f), L₂ = L₁ →
      LeanShared.PositiveFunctionalMeasure.measure L₂ h₂ = LeanShared.PositiveFunctionalMeasure.measure L₁ h₁ := by
    intro L₁ L₂ h₁ h₂ e
    subst e
    rfl
  rw [key _ _ _ _ hm, hv]

variable (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))

local instance prefixCompact (k : Fin ℓ) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D k N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D (k.val + 1) (by omega) (by omega))

set_option maxHeartbeats 1600000 in
/-- Derived families transport to any proportional chain family. -/
def Families.rescale (C₁ C₂ : NNReal → CanonicalChain X)
    (sf₁ : ∀ ε, 0 < ε → HasStrongFellerKernel (C₁ ε))
    (sf₂ : ∀ ε, 0 < ε → HasStrongFellerKernel (C₂ ε)) (c : ℝ) (hc : 0 < c)
    (scale : ∀ ε x, (C₂ ε).killedTransition x = ENNReal.ofReal c • (C₁ ε).killedTransition x)
    (d : Families T A hA Λ ℓ D t terminal root C₁ sf₁) :
    Families T A hA Λ ℓ D t terminal root C₂ sf₂ where
  window := d.window
  window_positive := d.window_positive
  data := fun s N ε hε hs => rankOneCongr (rankOneRescale (d.data s N ε hε hs) c hc)
    (restricted_transfer_scale (C₁ ε) (C₂ ε) c hc (scale ε) _ _ _ _).symm
  invariant := fun s N ε hε hs x hx => by
    rw [scale ε x, Measure.smul_apply, d.invariant s N ε hε hs x hx, smul_zero]
  zero_absorbing := fun ε hε x => by
    rw [scale ε x, Measure.smul_apply, d.zero_absorbing ε hε x, smul_zero]
  core_nonempty := d.core_nonempty
  core_positive := fun s N ε hε hs x hx => by
    rw [rankOneCongr_eigenvector, rankOneRescale_eigenvector]
    exact d.core_positive s N ε hε hs x hx
  core_support := fun s N ε hε hs => by
    rw [productMeasure_congr (C₁ ε) (C₂ ε) _ _ _ _ (d.data s N ε hε hs) _
      ((rankOneCongr_mean _ _).trans (rankOneRescale_mean _ _ _))
      ((rankOneCongr_eigenvector _ _).trans (rankOneRescale_eigenvector _ _ _))]
    exact d.core_support s N ε hε hs
  closedProduct := d.closedProduct
  base_product_identity := fun s ε hε hs => by
    rw [productMeasure_congr (C₁ ε) (C₂ ε) _ _ _ _ (d.data s 0 ε hε hs) _
      ((rankOneCongr_mean _ _).trans (rankOneRescale_mean _ _ _))
      ((rankOneCongr_eigenvector _ _).trans (rankOneRescale_eigenvector _ _ _))]
    exact d.base_product_identity s ε hε hs
  root_above_later := d.root_above_later
  closedProduct_probability := d.closedProduct_probability
  equilibrium := d.equilibrium
  localWeak := d.localWeak

end ConditionedStochasticStabilityHyperbolic.Global.FamiliesRescale
