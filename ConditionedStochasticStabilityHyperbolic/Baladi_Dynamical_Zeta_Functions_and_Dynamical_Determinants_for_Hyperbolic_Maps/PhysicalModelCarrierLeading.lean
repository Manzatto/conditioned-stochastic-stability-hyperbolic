module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierGenerator
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingRescale
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormInstances

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion
variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

namespace Data
variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/- The ordinary deterministic leading theorem is applied to the literal physical generator. This
contains no noisy gap, projector, measure or limit. -/
local instance leadingNormed : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed
local instance leadingSemi : SeminormedAddCommGroup m.strongCarrier := m.strongCarrierSemi
local instance leadingScalar : NormedSpace ℂ m.strongCarrier := m.strongCarrierScalar

open KellerLiverani1999
structure GeneratorLeading (a : Ω) where
  data : DeterministicLeading (m.carrierGenerator a)

namespace GeneratorLeading
variable {m} {a : Ω}

def rate (d : GeneratorLeading m a) : ℝ := d.data.rate

set_option synthInstance.maxHeartbeats 400000 in
/-- Raw normalization is a constructed datum, not another cited input. -/
def normalizeOfRaw (d : GeneratorLeading m a) {P : m.strongCarrier →L[ℂ] m.strongCarrier}
    (R : ℝ) (hR : 0 < R) (raw : (R : ℂ) • P = m.generator a) :
    DeterministicLeading P :=
  d.data.normalizeOfRaw R hR (raw.trans (by rfl))

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
set_option synthInstance.maxHeartbeats 400000 in
@[simp] theorem normalizeOfRaw_rate (d : GeneratorLeading m a)
    {P : m.strongCarrier →L[ℂ] m.strongCarrier}
    (R : ℝ) (hR : 0 < R) (raw : (R : ℂ) • P = m.generator a) :
    (d.normalizeOfRaw R hR raw).rate = R⁻¹ * d.rate := by
  exact DeterministicLeading.normalizeOfRaw_rate d.data R hR (raw.trans (by rfl))

end GeneratorLeading
end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
