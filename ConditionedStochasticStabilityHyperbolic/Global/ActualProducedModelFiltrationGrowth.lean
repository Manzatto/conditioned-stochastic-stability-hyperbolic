module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualPositiveNoiseFiltrationGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.ProducedModelHypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseEigenPressureGrowth

/-! # Actual punctured-noise filtration growth from individual spectral sources

The closed kernels, restricted reference densities and null complements are
constructed from the actual full noisy chain and shifted filtration geometry.
The source has only individual eigenfunction comparison outside the essential
radius. Physical spectral-radius inequalities and subordinate stratum bounds
are derived internally, and strong Feller is used only at positive noise.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualProducedModelFiltrationGrowth
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry ClosedLayerReference
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel FiltrationPressureConfinement
open KellerLiverani1999
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

local instance compactClosedLayer (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

theorem eventually_actual_stratum_bounds_from_produced_models
    (hA : IsOpen A)
    (hΛ : ∀ i : Fin ℓ, (Λ (D.index i)).Nonempty)
    (E Mid Weak : Fin ℓ → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
    [∀ i, NormedAddCommGroup (Mid i)] [∀ i, NormedSpace ℂ (Mid i)]
    [∀ i, NormedAddCommGroup (Weak i)] [∀ i, NormedSpace ℂ (Weak i)]
    [∀ i, CompleteSpace (Weak i)]
    (J : Finset (Fin ℓ)) (pressure : I → ℝ) (dominantPressure : ℝ)
    (hgap : ∀ i ∈ J, pressure (D.index i) < dominantPressure)
    (iH : ∀ i, (E i) →L[ℂ] (Mid i)) (iW : ∀ i, (E i) →L[ℂ] (Weak i))
    (law : NNReal → Measure Ξ) (prob : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : ∀ i, NNReal → Ξ → (E i) →L[ℂ] (E i)) (scale : Fin ℓ → ℝ)
    (models : ∀ i, ProducedAnnealedModel.Data (iH i) (iW i) law prob (generator i) (scale i))
    (essential : ∀ i, EssentialRadiusContract (E := E i) (W := Weak i))
    (hKL : ∀ i ∈ J, ClassicalConfinementContract (E := E i) (W := Weak i))
    (hdet : ∀ i ∈ J, spectralRadius ℂ ((scale i : ℂ) • (models i).inputs.operator 0) ≤
      ENNReal.ofReal (Real.exp (pressure (D.index i))))
    (hprincipal : ∀ i ∈ J, (models i).inputs.principal ≤ Real.exp (pressure (D.index i)))
    (dominantRate : NNReal → ℝ)
    (hdom : Tendsto dominantRate (𝓝 0) (𝓝 (Real.exp dominantPressure)))
    (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (hSF : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε)) (rawScale : Fin ℓ → ℝ)
    (hUltra : ∀ i ∈ J, StrongFellerSquareCompact.UltraFellerContract
      (X := closedLayer T A Λ ℓ N D i))
    (hFredholm : ∀ i ∈ J, PowerCompactGap.SquareCompactFredholm
      (F := closedLayer T A Λ ℓ N D i →ᵇ ℂ))
    (hcompare : ∀ i ∈ J, ∀ ε (hε : 0 < ε)
      (f : closedLayer T A Λ ℓ N D i →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (rawScale i • transferOperator (𝕜 := ℂ)
        (chain (C ε) (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))
        (strongFeller (C ε) (hSF ε hε) (closedLayer T A Λ ℓ N D i)
          (closedLayer_measurable T A Λ ℓ N D i))) f = z • f →
      (models i).inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • (models i).inputs.operator ε))
    (σ : Measure X) (q : NNReal → X × X → ENNReal)
    (hdensity : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x = σ.withDensity (fun y => q ε (x, y)))
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε, β < dominantRate ε ∧
      ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ)
          (chain (C ε) (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
          (strongFeller (C ε) (hSF ε hε) (stratum T A Λ ℓ N D i)
            (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ K * β ^ n := by
  have hall : ∀ i : Fin ℓ, ∃ h : Hypotheses (models i).inputs.operator
      (LeanShared.TwoNormNormalization.weakEmbedding (iW i)),
      h.alpha = (models i).inputs.principal / scale i ∧
      h.weakRate = (models i).inputs.weakRate / scale i := by
    intro i
    exact ProducedModelHypotheses.exists_actual_hypotheses (iH i) (iW i) law prob
      (generator i) (scale i) (models i) (essential i)
  choose hyp hα hweak using hall
  have hscale : ∀ i : Fin ℓ, 0 < scale i := fun i => zero_lt_one.trans_le (models i).inputs.scale_ge_one
  have hprincipalEq : ∀ i : Fin ℓ, scale i * (hyp i).alpha = (models i).inputs.principal := by
    intro i
    rw [hα i]
    field_simp [ne_of_gt (hscale i)]
  exact ActualPositiveNoiseFiltrationGrowth.eventually_actual_stratum_bounds_from_eigen_sources
    T A Λ ℓ N D hA hΛ E Weak J pressure dominantPressure hgap
    (fun i => (models i).inputs.operator)
    (fun i => LeanShared.TwoNormNormalization.weakEmbedding (iW i)) hyp hKL scale
    (fun i _ => hscale i) hdet (fun i hi => (hprincipalEq i).trans_le (hprincipal i hi))
    dominantRate hdom C hSF rawScale hUltra hFredholm
    (fun i hi ε hε f hf z he hz => hcompare i hi ε hε f hf z he ((hprincipalEq i) ▸ hz))
    σ q hdensity hpre hnull

end ConditionedStochasticStabilityHyperbolic.Global.ActualProducedModelFiltrationGrowth
