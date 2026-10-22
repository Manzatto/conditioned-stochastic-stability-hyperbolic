module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise
public import ConditionedStochasticStabilityHyperbolic.Spectral.HomeomorphicGapTransport
public import ConditionedStochasticStabilityHyperbolic.Spectral.FullNoiseSurvival

/-! The local theorem for the auxiliary system uses the literal live subtype
of the whole manifold. The stabilizing product uses the whole manifold as its
auxiliary state. Their actual killed kernels identify these two gaps. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.FullLiveNoiseGap
open LeanShared

variable {Y Ω : Type*} [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (F : Y × Ω → Y) (hF : Measurable F)
  (R : ℝ) (hR : 0 < R) (hOne : 1 ≤ R)

local notation "C" => NoiseKernel.chain ρ F hF univ MeasurableSet.univ
  (fun _ => 1) measurable_const R hR (fun _ => hOne)
local notation "D" => RestrictedNoise.chain ρ F hF univ MeasurableSet.univ
  (fun _ => 1) measurable_const R hR (fun _ => hOne)

omit [MetricSpace Y] [CompactSpace Y] [BorelSpace Y] in
/-- This is the actual noise kernel identity, without a supplied conjugacy
assumption or a choice of new auxiliary process. -/
theorem kernel_pushforward (y : (univ : Set Y)) :
    ((D).killedTransition y).map Subtype.val = (C).killedTransition y.val := by
  rw [RestrictedNoise.killedTransition_eq_restrict ρ F hF univ MeasurableSet.univ
    (fun _ => 1) measurable_const R hR (fun _ => hOne)
    (fun _ => 1) measurable_const (fun _ => hOne) (fun _ => rfl)]
  rw [SubtypeKernel.map_restrict_apply, Measure.restrict_univ]

omit [CompactSpace Y] [BorelSpace Y] in
/-- Strong Feller regularity on the actual whole manifold follows from the
local theorem's subtype process. -/
theorem strongFeller (sf : HasStrongFellerKernel D) : HasStrongFellerKernel C := by
  intro f hf hB
  have h := (sf (fun y => f y.val) (hf.comp measurable_subtype_coe)
    (by obtain ⟨B, hB, hb⟩ := hB; exact ⟨B, hB, fun y => hb y.val⟩)).comp
      (Homeomorph.Set.univ Y).symm.continuous
  convert h using 1
  ext y
  change (∫ z, f z ∂(C).killedTransition y) =
    ∫ z, f z.val ∂(D).killedTransition ((Homeomorph.Set.univ Y).symm y)
  have hk := kernel_pushforward ρ F hF R hR hOne ((Homeomorph.Set.univ Y).symm y)
  have he : ((Homeomorph.Set.univ Y).symm y).val = y :=
    (Homeomorph.Set.univ Y).apply_symm_apply y
  rw [he] at hk
  rw [← hk, integral_map_of_stronglyMeasurable measurable_subtype_coe hf.stronglyMeasurable]

omit [CompactSpace Y] in
/-- A gap produced by the local theorem supplies the gap of the actual fully
live auxiliary factor and its raw leading rate one. -/
theorem spectralData
    (sf : HasStrongFellerKernel D)
    (d : RankOneSpectralData (strongFellerTransferOperator D sf)
      (1 : (univ : Set Y) →ᵇ ℝ)) :
    ∃ d' : RankOneSpectralData
      (strongFellerTransferOperator C (strongFeller ρ F hF R hR hOne sf)) (1 : Y →ᵇ ℝ),
      R * d'.rate = 1 := by
  let e := (Homeomorph.Set.univ Y).symm
  let sd := strongFeller ρ F hF R hR hOne sf
  have hk (y : Y) : ((C).killedTransition y).map e = (D).killedTransition (e y) := by
    apply e.symm.measurableEmbedding.map_injective
    rw [Measure.map_map e.symm.measurable e.measurable]
    have he : e.symm ∘ e = id := by funext y; exact e.symm_apply_apply y
    rw [he, Measure.map_id]
    exact (kernel_pushforward ρ F hF R hR hOne (e y)).symm
  let d' := HomeomorphicGapTransport.transport e
    (strongFellerTransferOperator C sd) (strongFellerTransferOperator D sf) d
    (HomeomorphicGapTransport.intertwining e (C).killedTransition (D).killedTransition
      (strongFellerTransferOperator C sd) (strongFellerTransferOperator D sf)
      (strongFellerTransferOperator_represents C sd)
      (strongFellerTransferOperator_represents D sf) hk)
  exact ⟨d', FullNoiseSurvival.raw_rate ρ F hF R hR hOne sd d'⟩

end ConditionedStochasticStabilityHyperbolic.FullLiveNoiseGap
