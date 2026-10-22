module
public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapRetention
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalStableGapWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseRegularityChange

/-! The outcome of one literal local application, in a form independent of the regular space used
to prove it: the noise, laws and normalizer of the chain together with literal local stochastic
stability and gap retention. Its window family (local points, weak limit and normalized gaps on the
same probability measures) is constructed from these two conclusions. -/
public noncomputable section
open Set MeasureTheory Filter Bundle
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared
universe uX

structure NativeLocalOutcome
  {M : Type uX} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V) (ι : Type*) [Fintype ι]
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (w : K → ℝ) (φ : M → ℝ) where
  maps : RegularNoise.Maps (E := E) (ι := ι) T h.r
  laws : RegularNoise.Laws (ι := ι)
  scale : ℝ
  scale_positive : 0 < scale
  weight_continuous : Continuous w
  weight_bound : ∀ x, w x ≤ scale
  stability : LocalConclusions.Stability maps laws K Λ hK.measurableSet w
    weight_continuous.measurable scale scale_positive weight_bound
    (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x))
  retain : LocalConclusions.GapRetention maps laws K Λ hK.measurableSet w
    weight_continuous.measurable scale scale_positive weight_bound

namespace NativeLocalOutcome
variable
  {M : Type uX} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  {h : HL (E := E) T g Λ V} {ι : Type*} [Fintype ι]
  {K : Set M} [CompactSpace K] {hK : IsCompact K}
  {w : K → ℝ} {φ : M → ℝ}
  (d : NativeLocalOutcome h ι K hK w φ)

/-- The window family of a local outcome. -/
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

/-- The window family, constructed from stability and retention. -/
def family : Family d := Classical.choice (by
  obtain ⟨ν₀, νeq, hmap, heq, huniq, δ, hwindow, hδ, ν, limit, points, gaps⟩ :=
    LocalConclusions.stable_gap_window d.maps d.laws K Λ hK.measurableSet
      w d.weight_continuous.measurable d.scale d.scale_positive d.weight_bound
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) d.stability d.retain
  exact ⟨{ weight_continuous := d.weight_continuous
           weight_bound := d.weight_bound
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

/-- An outcome for one HL record is an outcome for any record with the same regularity and the
same unstable Jacobian. -/
@[expose] def transfer {g' : M → ℝ} {V' : Set M} {h' : HL (E := E) T g' Λ V'} (d : NativeLocalOutcome h' ι K hK w φ)
    (h : HL (E := E) T g Λ V) (hr : h'.r = h.r)
    (hJ : ∀ x, h'.basic.hyperbolic.unstableJacobian x = h.basic.hyperbolic.unstableJacobian x) :
    NativeLocalOutcome h ι K hK w φ where
  maps := d.maps.changeRegularity hr
  laws := d.laws
  scale := d.scale
  scale_positive := d.scale_positive
  weight_continuous := d.weight_continuous
  weight_bound := d.weight_bound
  stability := by
    have potential : (fun x => φ x - Real.log (h'.basic.hyperbolic.unstableJacobian x)) =
        (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) :=
      funext fun x => by rw [hJ x]
    have := d.stability
    rw [potential] at this
    exact (d.maps.stability_changeRegularity hr d.laws K Λ hK.measurableSet w
      d.weight_continuous.measurable d.scale d.scale_positive d.weight_bound _).mpr this
  retain := (LocalConclusions.gapRetention_changeRegularity d.maps d.laws K Λ hK.measurableSet w
    d.weight_continuous.measurable d.scale d.scale_positive d.weight_bound hr).mpr d.retain

theorem transfer_maps_family {g' : M → ℝ} {V' : Set M} {h' : HL (E := E) T g' Λ V'}
    (d : NativeLocalOutcome h' ι K hK w φ) (h : HL (E := E) T g Λ V) (hr : h'.r = h.r)
    (hJ : ∀ x, h'.basic.hyperbolic.unstableJacobian x = h.basic.hyperbolic.unstableJacobian x)
    (ε : ℝ≥0) : (d.transfer h hr hJ).maps.family ε = d.maps.family ε :=
  funext fun a => funext fun x => RegularNoise.Maps.changeRegularity_family d.maps hr ε a x

end NativeLocalOutcome
end ConditionedStochasticStabilityHyperbolic.Paper
