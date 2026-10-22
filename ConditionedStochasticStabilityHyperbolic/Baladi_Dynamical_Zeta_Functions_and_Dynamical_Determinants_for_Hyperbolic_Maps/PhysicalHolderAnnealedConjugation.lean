module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldCoreConjugation
public import LeanShared.Geometry.BoundedHolderConjugation
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! Ordinary cited anisotropic facts over the actual supported/full little
Hölder spaces. All regular realizations, dense cores, test inclusions and
physical compatibility identities are constructed, not source fields. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalHolderAnnealedConjugation
open LeanShared DyadicCompletion SmoothSupportedManifoldCore

variable {E U M AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

abbrev Regular (V : Set M) := SmoothHolderTestSpaces.space u holder V
abbrev FullTest := SmoothHolderTestSpaces.space u holder (univ : Set M)

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure K) [IsFiniteMeasure σ]


open KellerLiverani1999

def actual_conjugation
    (common : PhysicalHolderClassicalSources.Data u holder m K σ)
    (rows : PhysicalManifoldRowSources.Data m)
    (realCutoff : ∀ i x, star (m.localization.cutoff i x) = m.localization.cutoff i x)
    (evenAngle : ∀ i ξ, (m.angle i).toFun (-ξ) = (m.angle i).toFun ξ)
    {Noise W : Type*} [MeasurableSpace Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω)
    (i : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) i R)
    (generator_eq : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (ε : ℝ≥0) : RealOperatorConjugation (inputs.operator ε) := by
  have hn (c : PhysicalManifoldModel.Core (E := E) V) :
      ‖m.qa (SmoothSupportedManifoldCore.conjugate V c)‖ = ‖m.qa c‖ := by
    have hc := PhysicalManifoldCoreConjugation.norm_conjugate m.atlas m.localization m.atlas_mem V
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      realCutoff evenAngle c
    simpa only [DyadicCompletion.norm_coreLift, PhysicalManifoldModel.Data.qa] using hc
  have hJ (v : Regular u holder V) (x : M) :
      m.view (SmoothHolderTestSpaces.conjugate u holder V v) x = star (m.view v x) := by
    rw [common.view_eq u holder m K σ, common.view_eq u holder m K σ]
    exact SmoothHolderTestSpaces.view_conjugate u holder V v x
  have made := PhysicalModelAnnealedConjugation.actual_conjugation m rows
    (SmoothSupportedManifoldCore.conjugate V) (SmoothSupportedManifoldCore.conjugate_involutive V)
    (SmoothSupportedManifoldCore.conjugate_smul V) (fun _ _ => rfl) hn
    (SmoothHolderTestSpaces.conjugate u holder V) hJ law noise i R inputs generator_eq ε
  exact made

end ConditionedStochasticStabilityHyperbolic.PhysicalHolderAnnealedConjugation
