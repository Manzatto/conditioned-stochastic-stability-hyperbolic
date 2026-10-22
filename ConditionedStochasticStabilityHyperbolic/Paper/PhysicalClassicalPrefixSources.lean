module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayerFrame
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalNoiseDensity
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedGlobalAgreement
public import ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
public import ConditionedStochasticStabilityHyperbolic.Global.LiveFiltrationRealization

/-! Ordinary finite-stratum sources construct the global stochastic inputs. The actual anisotropic
inputs, compact inclusions, physical eigencomparison, strong-Feller property, density and
filtration support are all derived below. Strict trapping is an explicit additional gate: it is
not part of literal HG1. -/

public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory ProbabilityTheory IsManifold
open scoped Topology NNReal Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalPrefixSources
open LeanShared Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open PhysicalClassicalLayer KellerLiverani1999 ComplexStrongFeller RestrictedLayerChain
open FiltrationPressureConfinement DyadicCompletion SmoothSupportedManifoldCore
universe uM uE
variable {M : Type uM} {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  {ι I : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (A : Set M) (hA : IsOpen A) (Λ : I → Set M) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ) (w : M → ℝ) (R : ℝ) (pressure : I → ℝ)

local instance compactLayer (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem layerCompact (i : Fin ℓ) : IsCompact (closedLayer T A Λ ℓ N D i) :=
  isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)

variable (frames : ∀ i : Fin ℓ,
  Frame F σ (closedLayer T A Λ ℓ N D i) (layerCompact A Λ ℓ N D i) w R (pressure (D.index i)))

/- A chosen law defines the actual global chain through any selected frame.
Every other frame agrees on one positive noise germ by literal representation. -/
def actualChain (L : RegularNoise.Laws (ι := ι)) (j : Fin ℓ)
    (hw : Continuous w) (hR : 0 < R) (bound : ∀ x, w x ≤ R) (ε : ℝ≥0) :=
  NoiseKernel.chain (L.fixedLaw ε)
    (fun z : M × RegularNoise.FixedControl (ι := ι) =>
      (frames j).model.maps ((frames j).representation.fixedParameters ε z.2) z.1)
    ((frames j).representation.allScale_measurable ε) Aᶜ hA.measurableSet.compl
    w hw.measurable R hR bound

/- Actual map agreement is derived across heterogeneous parameter spaces;
there is no common stable dimension or common Whitney parameter requirement. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] [SecondCountableTopology M] in
theorem eventually_actual_each (L : RegularNoise.Laws (ι := ι)) (j i : Fin ℓ)
    (hw : Continuous w) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      actualChain F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound ε =
        NoiseKernel.chain (L.fixedLaw ε)
          (fun z : M × RegularNoise.FixedControl (ι := ι) =>
            (frames i).model.maps ((frames i).representation.fixedParameters ε z.2) z.1)
          ((frames i).representation.allScale_measurable ε) Aᶜ hA.measurableSet.compl
          w hw.measurable R hR bound := by
  filter_upwards [(frames j).representation.eventually_same_global_chain
    (frames i).representation Aᶜ hA.measurableSet.compl w hw.measurable R hR bound]
    with ε he
  exact he L

/- The actual killed chain is strong Feller on its genuine positive germ;
no smoothing assertion is made at deterministic noise zero. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] [SecondCountableTopology M] in
theorem eventually_strongFeller (L : RegularNoise.Laws (ι := ι)) (j : Fin ℓ)
    (hw : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (source : RegularNoise.SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι)) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      HasStrongFellerKernel (actualChain F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound ε) := by
  filter_upwards [(frames j).representation.eventually_global_strongFeller source Aᶜ
    hA.measurableSet.compl w hw nonnegative R hR bound] with ε he
  exact he L

/- The fixed absorbing zero level needs strict trapping. Positive levels
use only the ordinary compact adapted filtration, and one window covers all. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] [SecondCountableTopology M] in
theorem eventually_noUp (L : RegularNoise.Laws (ι := ι)) (j : Fin ℓ)
    (hw : Continuous w) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (strict : MapsTo T (closure A) A) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ i, i ≤ ℓ → ∀ x ∈ levels T A Λ ℓ N D i,
      (actualChain F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound ε).killedTransition
        x (levels T A Λ ℓ N D i)ᶜ = 0 := by
  filter_upwards [(frames j).representation.eventually_all_shifted_kernel_support
    N A hA strict D.levels ℓ D.compact_positive D.adapted_positive
    w hw.measurable R hR bound] with ε he
  exact he L

/- Absolute continuity is relative to ambient volume, including strata with
reference-null dangling boundary components. No nullity of the boundary of A
is required. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [σ.IsOpenPosMeasure] in
theorem exists_actual_density (L : RegularNoise.Laws (ι := ι)) (j : Fin ℓ)
    (hw : Continuous w) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    ∃ q : ℝ≥0 → M × M → ENNReal, (∀ ε, Measurable (q ε)) ∧
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
        (actualChain F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound ε).killedTransition x =
          σ.withDensity (fun y => q ε (x, y)) :=
  (frames j).representation.exists_global_density_family L σ
    (frames j).source.submersion Aᶜ hA.measurableSet.compl w hw.measurable R hR bound

end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalPrefixSources
