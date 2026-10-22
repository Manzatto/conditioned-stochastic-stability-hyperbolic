module

public import ConditionedStochasticStabilityHyperbolic.Paper.BoundedAdmissibleExponents
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionAnalyticPair
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedOrdinarySources
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
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair
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
abbrev Data := HLBoundedOrdinarySources.Data (E := E) (U := U) (M := M)
  (AtlasIndex := AtlasIndex) (Reg := Reg)
  (LocalReg := LocalReg) (A := A) (Ω := Ω) m h
  ((n).twoStepModel a a ha ha e e he he)
  ((n).intermediateModel a a ha ha e e he he)
  (expectedView) (ι := ι) (Order := Order)

namespace Data
variable (d : Data h expectedView m (ι := ι) (Order := Order))


def pressureCap : ℝ := max (Real.exp d.strong.pressure.equilibrium.pressure)
  (Real.exp d.intermediate.pressure.equilibrium.pressure)

/-- Actual cutoff norm on the compact ambient manifold. -/
def cutoffBound : ℝ := ‖BoundedContinuousFunction.mkOfCompact
  (⟨(n).weight, d.strong.pressure.weight_continuous⟩ : C(M, ℝ))‖

def principalS : ℝ := (d.strong.primitive _ h).pressure.ρ
def principalH : ℝ := (d.intermediate.primitive _ h).pressure.ρ

/-- Scalar arithmetic is checked independently of physical norm dictionaries. -/
def rates : BoundedRateChoice.Data
    (Real.exp d.strong.pressure.equilibrium.pressure)
    (Real.exp d.intermediate.pressure.equilibrium.pressure)
    (principalS h expectedView m d) (principalH h expectedView m d)
    d.strong.rows.weakBound d.intermediate.rows.weakBound d.normalizationFloor
    (cutoffBound h expectedView m d) :=
  BoundedRateChoice.choose _ _ _ _ _ _ _ _
    (d.strong.principal_lt_pressure _ h) (d.intermediate.principal_lt_pressure _ h)
    (norm_nonneg _)

def weakRate : ℝ := (rates h expectedView m d).weak
def scale : ℝ := (rates h expectedView m d).scale

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
theorem scale_ge_one : 1 ≤ scale h expectedView m d :=
  (rates h expectedView m d).scale_one

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
theorem scale_ge_floor : d.normalizationFloor ≤ scale h expectedView m d :=
  (rates h expectedView m d).scale_floor

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
theorem scale_positive : 0 < scale h expectedView m d :=
  lt_of_lt_of_le zero_lt_one (scale_ge_one h expectedView m d)

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
theorem weakRate_ge_pressure :
    Real.exp d.strong.pressure.equilibrium.pressure ≤ weakRate h expectedView m d ∧
    Real.exp d.intermediate.pressure.equilibrium.pressure ≤ weakRate h expectedView m d :=
  ⟨(rates h expectedView m d).pressure_strong,
   (rates h expectedView m d).pressure_intermediate⟩

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
theorem weight_le_scale (x : M) : (n).weight x ≤ scale h expectedView m d := by
  let w : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    (⟨(n).weight, d.strong.pressure.weight_continuous⟩ : C(M, ℝ))
  have hx : (n).weight x ≤ cutoffBound h expectedView m d :=
    (le_abs_self ((n).weight x)).trans (w.norm_coe_le_norm x)
  exact hx.trans (rates h expectedView m d).cutoff_scale

private def produced :=
  HLPreDistortionAnalyticPair.produced (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) n a a ha ha e e he he h
    d.maps d.laws d.representation d.strong d.intermediate d.reference d.reference_intermediate
    (weakRate h expectedView m d) (weakRate h expectedView m d)
    (scale h expectedView m d)
    (rates h expectedView m d).strong_principal
    (rates h expectedView m d).intermediate_principal
    (rates h expectedView m d).strong_step
    (rates h expectedView m d).intermediate_step
    (rates h expectedView m d).scale_one
    (rates h expectedView m d).strong_scale
    (rates h expectedView m d).intermediate_scale

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
private theorem strong_pressure_eq
    (eq : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g) :
    d.strong.pressure.equilibrium.pressure = eq.pressure :=
  EReal.coe_injective
    (d.strong.pressure.equilibrium.pressure_identity.symm.trans eq.pressure_identity)

omit [BorelSpace M] [T2Space M] [∀ i, CompleteSpace (LocalReg i)] in
private theorem intermediate_pressure_eq
    (eq : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g) :
    d.intermediate.pressure.equilibrium.pressure = eq.pressure :=
  EReal.coe_injective
    (d.intermediate.pressure.equilibrium.pressure_identity.symm.trans eq.pressure_identity)

omit [BorelSpace M] in
private theorem strong_principal_lt_equilibrium
    (eq : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g) :
    (produced h expectedView m d).pair.strong.principal < Real.exp eq.pressure := by
  rw [(produced h expectedView m d).principalS_eq,
    ← strong_pressure_eq h expectedView m d eq]
  exact d.strong.principal_lt_pressure _ h

omit [BorelSpace M] in
private theorem intermediate_principal_lt_equilibrium
    (eq : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g) :
    (produced h expectedView m d).pair.intermediate.principal < Real.exp eq.pressure := by
  rw [(produced h expectedView m d).principalH_eq,
    ← intermediate_pressure_eq h expectedView m d eq]
  exact d.intermediate.principal_lt_pressure _ h

omit [BorelSpace M] in
private theorem weakRates_ge_equilibrium
    (eq : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g) :
    Real.exp eq.pressure ≤ (produced h expectedView m d).pair.strong.weakRate ∧
    Real.exp eq.pressure ≤ (produced h expectedView m d).pair.intermediate.weakRate := by
  have hp := (weakRate_ge_pressure h expectedView m d).1
  have hpressure := congrArg Real.exp (strong_pressure_eq h expectedView m d eq)
  have hscalar : Real.exp eq.pressure ≤ weakRate h expectedView m d :=
    hpressure.symm.le.trans hp
  exact ⟨hscalar.trans_eq (produced h expectedView m d).weakRateS_eq.symm,
    hscalar.trans_eq (produced h expectedView m d).weakRateH_eq.symm⟩

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair
