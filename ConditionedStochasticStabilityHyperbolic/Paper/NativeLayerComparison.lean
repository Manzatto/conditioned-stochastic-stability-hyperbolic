module
public import ConditionedStochasticStabilityHyperbolic.Restriction.UniformWeightEigenmatching
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingUniqueness

/-! Original-weight spectrum comparison of one closed layer from the cutoff-weight analytic
eigenvectors (global route, native carriers). The analytic comparison of a carrier compares the
live chain with its own cutoff weight; on a separating retained collar where the cutoff weight is
the physical weight, the uniform raw-weight eigenmatching transports every large eigenvalue of the
physical-weight chain to the analytic spectrum. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerComparison
open LeanShared

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

/-- Every eigenvalue of the scaled live chain above `α` lies in the spectrum of the scaled operator
family. Stated once with generic instances, so concrete carriers can state it without synthesizing
the operator algebra of their analytic spaces. -/
def SpectrumComparison {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain Y) (R α : ℝ) (P : ℝ≥0 → E →L[ℂ] E) : Prop :=
  ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel (C ε),
    ∀ f : Y →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
      (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) (C ε) sf) f = z • f →
      α < ‖z‖ → z ∈ spectrum ℂ ((R : ℂ) • P ε)

theorem original_spectrum_of_cutoff_eigenvectors {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) [CompactSpace K]
    (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w wc : K → ℝ) (hw : Measurable w) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (agree : ∀ x : K, x.val ∈ closure U → w x = wc x)
    (P : ℝ≥0 → E →L[ℂ] E) (α : ℝ) (hα : 0 ≤ α)
    (close : ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x ∈ K, ∀ z, dist (F ε (x, z)) (T x) < η)
    (sfCut : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel
      (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR))
    (cut : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR),
      ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
        α < ‖z‖ → ∃ v : E, v ≠ 0 ∧ P ε v = z • v) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet w hw R hR hwR),
      ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
        α < ‖z‖ → z ∈ spectrum ℂ (P ε) := by
  obtain ⟨η, hη, lift⟩ := Restriction.exists_uniform_original_eigencomparison (Ω := Ω) (E := E)
    T K U hK hU hcore hUK hsep
  refine lift ρ F hF w wc hw hwc R hR hwR hwcR agree P (fun _ => α) (fun _ => hα) (close η hη)
    sfCut ?_
  filter_upwards [cut] with ε hc
  intro sf f hf z he hz
  obtain ⟨v, hv, hPv⟩ := hc sf f hf z he hz
  exact KellerLiverani1999.mem_spectrum_of_eigenvector (P ε) z v hv hPv

omit [CompactSpace X] in
/-- A layer spectrum comparison only depends on the noisy maps on the scales where they agree. -/
theorem spectrum_comparison_of_eventually_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F F' : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε)) (hF' : ∀ ε, Measurable (F' ε))
    (heq : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, F ε = F' ε)
    (K : Set X) (hK : MeasurableSet K) [CompactSpace K]
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (P : ℝ≥0 → E →L[ℂ] E) (α : ℝ)
    (h : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK w hw R hR hwR),
      ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
        α < ‖z‖ → z ∈ spectrum ℂ (P ε)) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F' ε) (hF' ε) K hK w hw R hR hwR),
      ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
        α < ‖z‖ → z ∈ spectrum ℂ (P ε) := by
  filter_upwards [heq, h] with ε he hc
  have key : ∀ (G : X × Ω → X) (hG : Measurable G), G = F' ε →
      (∀ sf : HasStrongFellerKernel (RestrictedNoise.chain (ρ ε) G hG K hK w hw R hR hwR),
        ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
          (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
          α < ‖z‖ → z ∈ spectrum ℂ (P ε)) →
      (∀ sf : HasStrongFellerKernel
          (RestrictedNoise.chain (ρ ε) (F' ε) (hF' ε) K hK w hw R hR hwR),
        ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
          (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
          α < ‖z‖ → z ∈ spectrum ℂ (P ε)) := by
    intro G hG hGe
    subst hGe
    exact id
  exact key (F ε) (hF ε) he hc

omit [CompactSpace X] in
/-- The spectrum comparison transfers between eventually equal map families. -/
theorem SpectrumComparison.of_eventually_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F F' : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε)) (hF' : ∀ ε, Measurable (F' ε))
    (heq : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, F ε = F' ε)
    (K : Set X) (hK : MeasurableSet K) [CompactSpace K]
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    {α : ℝ} {P : ℝ≥0 → E →L[ℂ] E}
    (h : SpectrumComparison (fun ε => RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK w hw R hR hwR)
      R α P) :
    SpectrumComparison (fun ε => RestrictedNoise.chain (ρ ε) (F' ε) (hF' ε) K hK w hw R hR hwR)
      R α P :=
  spectrum_comparison_of_eventually_eq ρ F F' hF hF' heq K hK w hw R hR hwR
    (fun ε => (R : ℂ) • P ε) α h

end ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerComparison
