module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerProductCorrespondence
public import ConditionedStochasticStabilityHyperbolic.Global.NestedLeadingData
public import ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationIntervalGrowth

/-!
# Actual selected gap from one dominant middle stratum and two aggregates

First assemble the subordinate lower prefix with the dominant stratum;
then add the subordinate upper interval. Both growth bounds concern actual
restricted chains, produced from finite pressure/KL and adapted filtration
geometry. No global gap, global eigenmeasure or QEM is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedGap
open ComplexStrongFeller LayerOperators RestrictedLayerChain NestedLayerKernel
open LayerRankOne LayerProductCorrespondence
private theorem cast_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P Q : E →L[ℝ] E} {one : E} (h : P = Q) (d : RankOneSpectralData P one) :
    (h ▸ d).rate = d.rate := by
  cases h
  rfl

private theorem cast_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P Q : E →L[ℝ] E} {one : E} (h : P = Q) (d : RankOneSpectralData P one) :
    (h ▸ d).eigenvector = d.eigenvector := by
  cases h
  rfl

private theorem cast_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P Q : E →L[ℝ] E} {one : E} (h : P = Q) (d : RankOneSpectralData P one) :
    (h ▸ d).mean = d.mean := by
  cases h
  rfl

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1) (h01 : L0 ⊆ L1)

local notation "C1" => chain C L1 hL1
local notation "sf1" => strongFeller C hSF L1 hL1
local notation "A0" => innerLevel L0 L1
local notation "ha0" => hL0.preimage measurable_subtype_coe

include h01 in
/-- The two-sided actual selected-prefix gap and exact dominant vector
restriction are derived from local data and subordinate growth alone. -/
theorem exists_selected_data_from_two_actual_aggregates
    (hs0 : ∀ x ∈ L0, C.killedTransition x L0ᶜ = 0)
    (hs1 : ∀ x ∈ L1, ∀ᵐ y ∂C.killedTransition x, y ∈ L1)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C1 sf1 A0 ha0)
      (1 : (A0ᶜ : Set L1) →ᵇ ℝ))
    {CA CD βA βD : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hβA : 0 ≤ βA) (hβD : 0 ≤ βD) (hArate : βA < d.rate) (hDrate : βD < d.rate)
    (hA : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L0 hL0)
      (strongFeller C hSF L0 hL0) ^ n‖ ≤ CA * βA ^ n)
    (hD : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L1ᶜ hL1.compl)
      (strongFeller C hSF L1ᶜ hL1.compl) ^ n‖ ≤ CD * βD ^ n) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = d.rate ∧
      (∀ y : (A0ᶜ : Set L1), dg.eigenvector y.val.val = d.eigenvector y) ∧
      ∀ f : X →ᵇ ℝ, dg.mean (f * dg.eigenvector) =
        d.mean ((restrictOperator A0ᶜ (restrictOperator L1 f)) * d.eigenvector) := by
  have hsA : ∀ x ∈ A0, ∀ᵐ y ∂(C1).killedTransition x, y ∈ A0 :=
    LiteralFiltrationGrowth.restricted_level_support C L0 L1 hL0 hL1 hs0
  have hAinner : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C1 sf1 A0 ha0 ^ n‖ ≤ CA * βA ^ n := by
    intro n
    rw [← transferOperator_eq_lower C1 sf1 A0 ha0]
    have he := nested_power_norm_eq (𝕜 := ℝ) L0 L1 h01 C hSF hL0 hL1 1 n
    simp only [one_smul] at he
    rw [he]
    exact hA n
  let d1 := globalDataWithSubordinateLower C1 sf1 A0 ha0 hsA d hCA hβA hArate hAinner
  have hrate1 : d1.rate = d.rate := lower_global_rate C1 sf1 A0 ha0 hsA d hCA hβA hArate hAinner
  have hDupper : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L1 hL1 ^ n‖ ≤ CD * βD ^ n := by
    intro n
    change ‖lowerOperator (𝕜 := ℝ) C hSF L1ᶜ hL1.compl ^ n‖ ≤ CD * βD ^ n
    rw [← transferOperator_eq_lower C hSF L1ᶜ hL1.compl]
    exact hD n
  have hdlower : transferOperator (𝕜 := ℝ) C1 sf1 = lowerOperator (𝕜 := ℝ) C hSF L1 hL1 :=
    transferOperator_eq_lower C hSF L1 hL1
  let d1lower : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L1 hL1) (1 : L1 →ᵇ ℝ) :=
    hdlower ▸ d1
  have hrateLower : d1lower.rate = d.rate := (cast_rate hdlower d1).trans hrate1
  have hdr : βD < d1lower.rate := hrateLower.symm ▸ hDrate
  let dg := globalDataWithSubordinateUpper C hSF L1 hL1 hs1 d1lower hCD hβD hdr hDupper
  refine ⟨dg, (upper_global_rate C hSF L1 hL1 hs1 d1lower hCD hβD hdr hDupper).trans hrateLower, ?_, ?_⟩
  · intro y
    have he1 := lower_global_vector_restrict C1 sf1 A0 ha0 hsA d hCA hβA hArate hAinner
    have he2 := upper_global_vector_restrict C hSF L1 hL1 hs1 d1lower hCD hβD hdr hDupper
    have hy2 := congrArg (fun f : L1 →ᵇ ℝ => f y.val) he2
    have hy1 := congrArg (fun f : (A0ᶜ : Set L1) →ᵇ ℝ => f y) he1
    change dg.eigenvector y.val.val = d1lower.eigenvector y.val at hy2
    change d1.eigenvector y.val = d.eigenvector y at hy1
    have hvec : d1lower.eigenvector = d1.eigenvector := cast_vector hdlower d1
    exact hy2.trans (hvec ▸ hy1)
  · intro f
    rw [upper_global_product_pairing C hSF L1 hL1 hs1 d1lower hCD hβD hdr hDupper f]
    have hm : d1lower.mean = d1.mean := cast_mean hdlower d1
    have hv : d1lower.eigenvector = d1.eigenvector := cast_vector hdlower d1
    rw [hm, hv]
    exact lower_global_product_pairing C1 sf1 A0 ha0 hsA d hCA hβA hArate hAinner (restrictOperator L1 f)

end ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedGap
