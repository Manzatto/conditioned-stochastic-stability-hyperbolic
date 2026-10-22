module

public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeChains
public import ConditionedStochasticStabilityHyperbolic.Paper.ExponentialWeight
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Literal targets for the two local manuscript theorems. The process uses the actual shrinking
control cube; its normalization scale is shared by both eigenrelations and the raw spectral
radius. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The full spectral/product conclusion, including the finite left measure
and the normalization, rather than only existence of a QEM. -/
structure SpectralWitness (C : AbsorbingMarkovChains.CanonicalChain X)
    (R : ℝ) (ν : ProbabilityMeasure X) where
  strongFeller : HasStrongFellerKernel C
  eigenfunction : X →ᵇ ℝ
  eigenfunction_nonnegative : ∀ x, 0 ≤ eigenfunction x
  eigenmeasure : Measure X
  finite_eigenmeasure : IsFiniteMeasure eigenmeasure
  rate : ℝ
  rate_positive : 0 < rate
  right : (R • strongFellerTransferOperator C strongFeller) eigenfunction =
    rate • eigenfunction
  left : ∀ f : X →ᵇ ℝ,
    (∫ x, ((R • strongFellerTransferOperator C strongFeller) f) x ∂eigenmeasure) =
      rate * ∫ x, f x ∂eigenmeasure
  normalization : ∫ x, eigenfunction x ∂eigenmeasure = 1
  product : (ν : Measure X) = eigenvectorMeasure eigenmeasure eigenfunction
  radius : spectralRadius ℝ (R • strongFellerTransferOperator C strongFeller) =
    ENNReal.ofReal rate

/-- Qualified uniqueness is exactly the qualification in thm:qem-local.
The QEM definition quantifies over every bounded measurable observable. -/
def Point (C : AbsorbingMarkovChains.CanonicalChain X) (R : ℝ)
    (core : Set X) (ν : ProbabilityMeasure X) : Prop :=
  C.IsQuasiErgodic (ν : Measure X) ∧ core ⊆ (ν : Measure X).support ∧
    (∀ ζ : Measure X, C.IsQuasiErgodic ζ → core ⊆ ζ.support → ζ = (ν : Measure X)) ∧
    Nonempty (SpectralWitness C R ν)

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

/-- The local existence theorem with one positive window chosen before
initial states and observables. The chain is the literal original law. -/
def Existence : Prop :=
  ∃ δ : ℝ≥0, ∃ hwindow : δ ≤ F.window, 0 < δ ∧
    ∃ ν : ℝ≥0 → ProbabilityMeasure K, ∀ ε : ℝ≥0, (hε : 0 < ε) → (hδ : ε ≤ δ) →
      Point (RestrictedNoise.chain (L.law ε)
        (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε (hδ.trans hwindow)) K hK w hw R hR hwR)
        R {x : K | x.val ∈ Λ} (ν ε)

omit [FiniteDimensional ℝ E] [CompactSpace K] in
/-- Exact correspondence transfers the full local conclusion, including
left/right eigenrelations and radius, from fixed controls to shrinking cubes. -/
theorem existence_of_fixed_cube
    (δ : ℝ≥0) (hδ : 0 < δ) (hwindow : δ ≤ F.window)
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (h : ∀ ε : ℝ≥0, (hε : 0 < ε) → (hεδ : ε ≤ δ) →
      Point (RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
        (F.fixedMap_measurable ε hε (hεδ.trans hwindow)) K hK w hw R hR hwR)
        R {x : K | x.val ∈ Λ} (ν ε)) :
    Existence F L K Λ hK w hw R hR hwR := by
  refine ⟨δ, hwindow, hδ, ν, ?_⟩
  intro ε hε hεδ
  rw [← F.chain_fixed_cube L ε hε (hεδ.trans hwindow) K hK w hw R hR hwR]
  exact h ε hε hεδ

/-- The second local theorem uses the same QEM family and the genuine
entropy/pressure equilibrium definition. The limit on K pushes forward to
the equilibrium state on M; no equilibrium property is replaced by a name. -/
def Stability (potential : M → ℝ) : Prop :=
  ∃ ν₀ : ProbabilityMeasure K, ∃ νeq : ProbabilityMeasure M,
    (ν₀ : Measure K).map Subtype.val = (νeq : Measure M) ∧
    ThermodynamicDefinitions.IsEquilibriumState T potential Λ νeq ∧
    (∀ ζ : ProbabilityMeasure M,
      ThermodynamicDefinitions.IsEquilibriumState T potential Λ ζ → ζ = νeq) ∧
    ∃ δ : ℝ≥0, ∃ hwindow : δ ≤ F.window, 0 < δ ∧
      ∃ ν : ℝ≥0 → ProbabilityMeasure K,
        Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
        ∀ ε : ℝ≥0, (hε : 0 < ε) → (hδ : ε ≤ δ) →
          Point (RestrictedNoise.chain (L.law ε)
            (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
            (F.raw_measurable ε hε (hδ.trans hwindow)) K hK w hw R hR hwR)
            R {x : K | x.val ∈ Λ} (ν ε)

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem Stability.existence {potential : M → ℝ}
    (h : Stability F L K Λ hK w hw R hR hwR potential) :
    Existence F L K Λ hK w hw R hR hwR := by
  obtain ⟨ν₀, νeq, _, _, _, δ, hwindow, hδ, ν, _, hν⟩ := h
  exact ⟨δ, hwindow, hδ, ν, hν⟩

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
