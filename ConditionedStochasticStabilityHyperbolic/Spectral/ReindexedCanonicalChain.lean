module

public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.HomeomorphicGapTransport

/-! Construct the absorbing process after a genuine live-state coordinate
change. Its killed kernel and strong-Feller property are derived. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionedStochasticStabilityHyperbolic.ReindexedCanonicalChain

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (e : X ≃ₜ Y) (C : AbsorbingMarkovChains.CanonicalChain Y)

def liveKernel : Kernel X X :=
  (C.killedTransition.comap e e.measurable).map e.symm

@[simp] theorem liveKernel_apply (x : X) :
    liveKernel e C x = (C.killedTransition (e x)).map e.symm := by
  exact Kernel.map_apply _ e.symm.measurable x

theorem liveKernel_mass (x : X) : liveKernel e C x univ ≤ 1 := by
  rw [liveKernel_apply, Measure.map_apply e.symm.measurable MeasurableSet.univ, preimage_univ]
  exact C.killedTransition_mass_le_one (e x)

def chain : AbsorbingMarkovChains.CanonicalChain X :=
  WeightedKernel.ofSubMarkov (liveKernel e C) (liveKernel_mass e C)

@[simp] theorem killed (x : X) :
    (chain e C).killedTransition x = (C.killedTransition (e x)).map e.symm := by
  rw [chain, WeightedKernel.ofSubMarkov_killedTransition, liveKernel_apply]

theorem kernel_pushforward (x : X) :
    ((chain e C).killedTransition x).map e = C.killedTransition (e x) := by
  rw [killed, Measure.map_map e.measurable e.symm.measurable]
  simp only [Function.comp_def, e.apply_symm_apply, Measure.map_id']

theorem strongFeller (sf : HasStrongFellerKernel C) : HasStrongFellerKernel (chain e C) := by
  intro f hf hB
  have h := (sf (fun y => f (e.symm y)) (hf.comp e.symm.measurable)
    (by obtain ⟨B, hB, hb⟩ := hB; exact ⟨B, hB, fun y => hb (e.symm y)⟩)).comp e.continuous
  convert h using 1
  ext x
  rw [killed, integral_map_of_stronglyMeasurable e.symm.measurable hf.stronglyMeasurable]
  rfl

end ConditionedStochasticStabilityHyperbolic.ReindexedCanonicalChain
