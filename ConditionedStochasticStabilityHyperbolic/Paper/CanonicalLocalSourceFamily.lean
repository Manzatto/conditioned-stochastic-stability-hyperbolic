module
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceParameters
import all ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalStableGapWindow

/-! One family is constructed from ordinary local sources. Its local points,
weak limit and normalized gaps use the same probability measures and window. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
open LeanShared
universe uX
variable
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
  {h : HL (E := E) T g Λ V}
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  {K : Set M} [CompactSpace K] {hK : IsCompact K}
  {hΛ : isolatedCore T K = Λ} {hΛK : Λ ⊆ K}
  {w : K → ℝ} {φ : M → ℝ}
  {σ : Measure M} [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (d : CanonicalLocalSources (U := U) (AtlasIndex := AtlasIndex) (A := A) (Ω := Ω)
    (LocalReg := LocalReg) (S := S) (μ := μ) (ι := ι) (Order := Order)
    h K hK hΛ hΛK w φ σ)


structure Family where
  weight_continuous : Continuous w
  weight_bound : ∀ x, w x ≤ d.scale
  initialLimit : ProbabilityMeasure K
  equilibrium : ProbabilityMeasure M
  map_limit : (initialLimit : Measure K).map Subtype.val = (equilibrium : Measure M)
  equilibrium_state : ThermodynamicDefinitions.IsEquilibriumState T
    (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ equilibrium
  equilibrium_unique : ∀ ζ : ProbabilityMeasure M,
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ ζ → ζ = equilibrium
  window : ℝ≥0
  window_bound : window ≤ d.maps.window
  window_positive : 0 < window
  probability : ℝ≥0 → ProbabilityMeasure K
  limit : Tendsto probability (𝓝[>] (0 : ℝ≥0)) (𝓝 initialLimit)
  point : ∀ ε (hε : 0 < ε) (hwindow : ε ≤ window),
    LocalConclusions.Point
      (RestrictedNoise.chain (d.laws.law ε)
        (fun z : M × RegularNoise.cube (ι := ι) ε => d.maps.family ε z.2.val z.1)
        (d.maps.raw_measurable ε hε (hwindow.trans window_bound)) K hK.measurableSet
        w weight_continuous.measurable d.scale d.scale_positive weight_bound)
      d.scale {x | x.val ∈ Λ} (probability ε)
  gap : ∀ ε (_hε : 0 < ε) (_hwindow : ε ≤ window),
    LocalConclusions.NormalizedGapAt d.maps d.laws K Λ hK.measurableSet
      w weight_continuous.measurable d.scale d.scale_positive weight_bound (probability ε) ε

private def family : Family d := Classical.choice (by
  obtain ⟨hw, bound, stability, retain⟩ := stability_and_retention d
  obtain ⟨ν₀, νeq, hmap, heq, huniq, δ, hwindow, hδ, ν, limit, points, gaps⟩ :=
    LocalConclusions.stable_gap_window d.maps d.laws K Λ hK.measurableSet
      w hw.measurable d.scale d.scale_positive bound
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) stability retain
  exact ⟨{ weight_continuous := hw
           weight_bound := bound
           initialLimit := ν₀
           equilibrium := νeq
           map_limit := hmap
           equilibrium_state := heq
           equilibrium_unique := huniq
           window := δ
           window_bound := hwindow
           window_positive := hδ
           probability := ν
           limit := limit
           point := points
           gap := gaps }⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
