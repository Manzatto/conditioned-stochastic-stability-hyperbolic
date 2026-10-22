module

public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixNormalizedGap
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralNoiseLiveChain

/-! Actual noise kernels killed outside Aᶜ give the literal local noise
chain on a live prefix P\A. Its full gap and same product probability are
derived from the global prefix datum, including the kernel identification. -/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualLivePrefixNormalizedGap
open LeanShared RandomMapKernel WeightedConditioning LayerQuasiErgodic ComplexStrongFeller
variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
  (P A : Set X) (hP : IsCompact P) (hA : IsOpen A)
  (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
local notation "C" => NoiseKernel.chain ρ F hF Aᶜ hA.measurableSet.compl w hw R hR bound
local notation "hK" => hP.measurableSet.diff hA.measurableSet
local notation "CP" => RestrictedLayerChain.chain C P hP.measurableSet
set_option quotPrecheck false in
local notation "CL" => RestrictedNoise.chain ρ F hF (P \ A) hK
  (fun x : ↥(P \ A) => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val)

/-- Absorption in A is an exact property of the constructed noise kernel. -/
theorem zero_absorbing : ∀ x, (C).killedTransition x A = 0 := by
  intro x
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.smul_apply, smul_eq_mul]
  change ENNReal.ofReal (w x / R) * ((transition ρ F hF x).restrict Aᶜ) A = 0
  rw [Measure.restrict_apply hA.measurableSet]
  simp only [inter_compl_self, measure_empty, mul_zero]

/-- No prefix mixing or independently supplied live gap is needed. -/
theorem exists_normalizedGap
    (sf : HasStrongFellerKernel C)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP
      (RestrictedLayerChain.strongFeller C sf P hP.measurableSet)) (1 : P →ᵇ ℝ))
    (Λ : Set X) (positive : ∀ x : P, x.val ∈ Λ → 0 < d.eigenvector x) :
    letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    letI : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
    ∃ ν : ProbabilityMeasure ↥(P \ A),
      Paper.LocalConclusions.NormalizedGap CL {x : ↥(P \ A) | x.val ∈ Λ} ν ∧
      (ν : Measure ↥(P \ A)).map Subtype.val =
        (productMeasure CP (RestrictedLayerChain.strongFeller C sf P hP.measurableSet) d).map Subtype.val := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  have produced := LivePrefixNormalizedGap.exists_normalizedGap P A hP hA C sf
    (zero_absorbing ρ F hF A hA w hw R hR bound) d Λ positive
  let ν := Classical.choose produced
  have properties := Classical.choose_spec produced
  have actual := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction ρ F hF
    Aᶜ (P \ A) hA.measurableSet.compl hK (fun _ hx => hx.2) w hw R hR bound
  exact ⟨ν, actual.symm ▸ properties.1, properties.2⟩

end ConditionedStochasticStabilityHyperbolic.Global.ActualLivePrefixNormalizedGap
