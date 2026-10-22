module
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalStableGapWindow
import all ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalConsumer
import all ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalGaps

/-! Actual selected ordinary sources produce the same probability family
with its literal local conclusions, weak limit, and normalized gaps. This
is the source application used before stabilizing-product descent. -/
public noncomputable section
set_option maxHeartbeats 3200000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX
private theorem stable_family
  {M : Type uX} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (ms mh : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space (u) holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (hΛ : isolatedCore T K = Λ) (hΛK : Λ ⊆ K)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {ι : Type*} [Fintype ι]
  (N : RegularNoise.Maps (E := E) (ι := ι) T h.r)
  (L : RegularNoise.Laws (ι := ι))
  (representation : RegularNoise.Representation N Ω mh.maps)
  (w : K → ℝ) (R : ℝ) (hR : 0 < R)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (c : Data (Carrier := mh.StrongSpace) (W := W) h u holder ms mh K hK hΛ hΛK N L representation w R hR σ)
  (i : ms.StrongSpace →L[ℂ] mh.StrongSpace) (j : mh.StrongSpace →L[ℂ] W)
  (p : ProducedAnnealedPair.Data i j L.fixedLaw (fun _ => inferInstance)
    (fun ε z => ms.generator (representation.fixedParameters ε z))
    (fun ε z => mh.generator (representation.fixedParameters ε z)) R)
  (principalS : p.strong.principal < Real.exp c.equilibrium.pressure)
  (principalH : p.intermediate.principal < Real.exp c.equilibrium.pressure)
  (weakS : Real.exp c.equilibrium.pressure ≤ p.strong.weakRate)
  (weakH : Real.exp c.equilibrium.pressure ≤ p.intermediate.weakRate) :
  ∃ (ν₀ : ProbabilityMeasure K) (νeq : ProbabilityMeasure M),
    (ν₀ : Measure K).map Subtype.val = (νeq : Measure M) ∧
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => c.φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ νeq ∧
    (∀ ζ : ProbabilityMeasure M, ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => c.φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ ζ → ζ = νeq) ∧
    ∃ (δ : ℝ≥0) (hwindow : δ ≤ N.window), 0 < δ ∧
    ∃ ν : ℝ≥0 → ProbabilityMeasure K,
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      (∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
        LocalConclusions.Point (RestrictedNoise.chain (L.law ε)
          (fun z : M × RegularNoise.cube (ι := ι) ε => N.family ε z.2.val z.1)
          (N.raw_measurable ε hε (hεδ.trans hwindow)) K hK.measurableSet w
          c.hw.measurable R hR c.hwR) R {x | x.val ∈ Λ} (ν ε)) ∧
      ∀ ε (_hε : 0 < ε) (_hεδ : ε ≤ δ), LocalConclusions.NormalizedGapAt N L K Λ
        hK.measurableSet w c.hw.measurable R hR c.hwR (ν ε) ε := by
  have stability := consume h u holder ms mh K hK hΛ hΛK N L representation w R hR σ
    c i j p principalS principalH weakS weakH
  exact LocalConclusions.stable_gap_window N L K Λ hK.measurableSet w c.hw.measurable
    R hR c.hwR (fun x => c.φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) stability
    (fun ν points => retain_gaps h u holder ms mh K hK hΛ hΛK N L representation w R hR σ
      c i j p principalH weakH ν points)

end ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
