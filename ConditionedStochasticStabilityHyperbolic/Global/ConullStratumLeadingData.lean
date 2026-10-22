module

public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
public import ConditionedStochasticStabilityHyperbolic.Global.LayerRankOne
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodic

/-!
# Dominant closed-layer leading data descend to the literal conull stratum

The actual conull-boundary kernel factorization constructs the stratum gap.
The eigenvector is a positive multiple of restriction. Its left measure is
constructed from the closed-layer left measure; neither a literal-stratum
spectral gap nor a new noisy eigenmeasure is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.ConullStratumLeadingData
open ComplexStrongFeller LayerOperators LayerRankOne RestrictedLayerChain
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U)
  (hzero : ∀ x, C.killedTransition x Uᶜ = 0)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))

/-- Reversed actual smoothing/restriction factors construct the literal
stratum's leading spectral data. -/
def stratumData : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
    (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ) := by
  have hQ : transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU) =
      (restrictOperator (𝕜 := ℝ) U).comp (extensionOperator C hSF U hU) := by
    rw [transferOperator_eq_lower]
    rfl
  exact liftedData (restrictOperator U) (extensionOperator C hSF U hU) hQ
    (NullBoundaryLayer.transfer_eq_extension_restriction C hSF U hU hzero) d

theorem stratumData_rate : (stratumData C hSF U hU hzero d).rate = d.rate := rfl

theorem stratumData_vector (x : U) :
    (stratumData C hSF U hU hzero d).eigenvector x = d.rate⁻¹ * d.eigenvector x.val := rfl

theorem stratumData_vector_pos (x : U) (hx : 0 < d.eigenvector x.val) :
    0 < (stratumData C hSF U hU hzero d).eigenvector x :=
  mul_pos (inv_pos.mpr d.rate_pos) hx

variable (μ : Measure X) [IsFiniteMeasure μ]
  (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)

include hU hzero hmean in
/-- The actual leading measure ignores the removed conull stratum boundary;
this follows from its derived eigenmeasure law, rather than being assumed. -/
theorem leading_measure_ae_stratum : ∀ᵐ x ∂μ, x ∈ U := by
  let : IsFiniteKernel C.killedTransition := ⟨⟨1, by simp, C.killedTransition_mass_le_one⟩⟩
  have hleft := rankOne_left_eigenmeasure d C.killedTransition (transferOperator_apply C hSF) μ hmean
  have hs : ∀ᵐ x ∂μ, ∀ᵐ y ∂C.killedTransition x, y ∈ U := by
    apply ae_of_all
    intro x
    rw [ae_iff]
    exact hzero x
  have ha := Measure.ae_comp_of_ae_ae hU hs
  rw [hleft] at ha
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr d.rate_pos).ne').mp ha

/-- The constructed literal-stratum left measure compensates the positive
inverse-rate eigenvector scaling. -/
def stratumMeasure : Measure U := ENNReal.ofReal d.rate • μ.comap Subtype.val

omit [MetricSpace X] [BorelSpace X] in
include hU in
private theorem finite_comap : IsFiniteMeasure (μ.comap (Subtype.val : U → X)) := by
  constructor
  rw [(MeasurableEmbedding.subtype_coe hU).comap_apply]
  exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top μ univ)

include hU in
theorem stratumMeasure_finite : IsFiniteMeasure (stratumMeasure C hSF U d μ) := by
  let : IsFiniteMeasure (μ.comap (Subtype.val : U → X)) := finite_comap U hU μ
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

include hU hzero hmean in
/-- Actual bounded-continuous leading-functional representation on the
literal stratum is produced from the closed-layer representation. -/
theorem stratumMeasure_represents (f : U →ᵇ ℝ) :
    (stratumData C hSF U hU hzero d).mean f = ∫ x, f x ∂stratumMeasure C hSF U d μ := by
  let : IsFiniteKernel C.killedTransition := ⟨⟨1, by simp, C.killedTransition_mass_le_one⟩⟩
  let fe := LeanShared.SubtypeKernel.zeroExtend U f
  have hfe : Measurable fe := LeanShared.SubtypeKernel.measurable_zeroExtend U hU f f.continuous.measurable
  have hfi : Integrable fe μ := Integrable.of_bound hfe.aestronglyMeasurable ‖f‖
    (ae_of_all _ (LeanShared.SubtypeKernel.norm_zeroExtend_le U f ‖f‖ (norm_nonneg _) f.norm_coe_le_norm))
  have hleft := rankOne_integral_kernel d C.killedTransition (transferOperator_apply C hSF) μ hmean fe hfi
  have hsub : (∫ y : U, f y ∂μ.comap Subtype.val) = ∫ y, fe y ∂μ := by
    calc
      _ = ∫ y : U, fe y.val ∂μ.comap Subtype.val := by simp only [fe, LeanShared.SubtypeKernel.zeroExtend_coe]
      _ = ∫ y in U, fe y ∂μ := integral_subtype_comap hU fe
      _ = _ := by rw [Measure.restrict_eq_self_of_ae_mem (leading_measure_ae_stratum C hSF U hU hzero d μ hmean)]
  change d.mean (extensionOperator C hSF U hU f) = _
  rw [hmean]
  change (∫ x, ∫ y, fe y ∂C.killedTransition x ∂μ) = _
  rw [hleft, stratumMeasure, integral_smul_measure, ENNReal.toReal_ofReal d.rate_pos.le, smul_eq_mul, hsub]

end ConditionedStochasticStabilityHyperbolic.Global.ConullStratumLeadingData
