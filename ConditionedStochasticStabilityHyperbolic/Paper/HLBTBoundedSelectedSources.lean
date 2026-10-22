module

public import ConditionedStochasticStabilityHyperbolic.Paper.BoundedAdmissibleExponents
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionAnalyticPair
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedOrdinarySources
public import ConditionedStochasticStabilityHyperbolic.Paper.BoundedRateChoice

/-! A fixed canonical loss tower on an already selected physical model feeds
the strongest ordinary-source analytic producer. Its regular space and model
stay abstract; the concrete caller constructs the bounded canonical exponents.
Normalization rates are derived internally. The strongest
ordinary sources retain their explicit saddle-dimension hypotheses. Source
records contain no compactness, random robust block, gap or QEM fields. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedSelectedSources
open LeanShared KellerLiverani1999 Paper.RegularNoise
open BoundedAdmissibleExponents

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (expectedView : Reg → M → ℂ)
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

local notation "n" => m
local notation "η" => loss h.r
local notation "a" => (fun _ : m.localization.indices => η)
local notation "ha" => (fun _ : m.localization.indices => loss_positive h.regularity_gt_one)
local notation "e" => (fun (_ : m.localization.indices) (_ : Bool) => (0 : ℝ))
local notation "he" => (fun (_ : m.localization.indices) (_ : Bool) => (le_rfl : (0 : ℝ) ≤ 0))

@[expose] def strongModel := (n).twoStepModel a a ha ha e e he he
@[expose] def intermediateModel := (n).intermediateModel a a ha ha e e he he

variable {ι Order : Type*} [Fintype ι] [Fintype Order]

/-- Canonical actual regular space and physical exponents specialize an
already checked generic ordinary-source record; no scalar admissibility fields. -/
abbrev Data := HLBTBoundedOrdinarySources.Data (E := E) (U := U) (M := M)
  (AtlasIndex := AtlasIndex) (Reg := Reg)
  (LocalReg := LocalReg) (A := A) (Ω := Ω) m h
  ((n).twoStepModel a a ha ha e e he he)
  ((n).intermediateModel a a ha ha e e he he)
  (expectedView) (ι := ι) (Order := Order)

namespace Data
variable (d : Data h expectedView m (ι := ι) (Order := Order))

/-- Exact ordinary BT formulas and adapted geometry feed the canonical
actual selected-model consumer. The determinant-cover bound is proved
inside this conversion, never requested as a source field. -/
@[expose] def classical : HLBoundedSelectedAnalyticPair.Data h expectedView m
    (ι := ι) (Order := Order) :=
  HLBTBoundedOrdinarySources.Data.classical m h (m.twoStepModel a a ha ha e e he he)
    (m.intermediateModel a a ha ha e e he he) expectedView d

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedSelectedSources
