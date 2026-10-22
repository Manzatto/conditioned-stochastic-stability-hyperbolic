module

public import ConditionedStochasticStabilityHyperbolic.Global.EventualProducedModelFiltrationGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.ProducedModelHypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseEigenPressureGrowth

/-! # Actual punctured-noise filtration growth from individual spectral sources

The closed kernels, restricted reference densities and null complements are
constructed from the actual full noisy chain and shifted filtration geometry.
The source has only individual eigenfunction comparison outside the essential
radius. Physical spectral-radius inequalities and subordinate stratum bounds
are derived internally, and strong Feller is used only at positive noise.
-/
public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.EventualDominantPressureGrowth
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry ClosedLayerReference
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel FiltrationPressureConfinement
open KellerLiverani1999
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

local instance compactClosedLayer (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

theorem eventually_stratum_bounds_from_actual_projector_rate
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
    (j : Fin ℓ)
    (det : DeterministicLeading ((models j).inputs.operator 0)) (cutoff margin : ℝ)
    (outputs : ProjectorOutputs (models j).inputs.operator
      (LeanShared.TwoNormNormalization.weakEmbedding (iW j)) det cutoff margin)
    (hpressure : scale j * det.rate = Real.exp dominantPressure)
    (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (hSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε))
    (rawScale : Fin ℓ → ℝ)
    (hUltra : ∀ i ∈ J, StrongFellerSquareCompact.UltraFellerContract
      (X := closedLayer T A Λ ℓ N D i))
    (hFredholm : ∀ i ∈ J, PowerCompactGap.SquareCompactFredholm
      (F := closedLayer T A Λ ℓ N D i →ᵇ ℂ))
    (hcompare : ∀ i ∈ J, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (sf : HasStrongFellerKernel (C ε))
      (f : closedLayer T A Λ ℓ N D i →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (rawScale i • transferOperator (𝕜 := ℂ)
        (chain (C ε) (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))
        (strongFeller (C ε) sf (closedLayer T A Λ ℓ N D i)
          (closedLayer_measurable T A Λ ℓ N D i))) f = z • f →
      (models i).inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • (models i).inputs.operator ε))
    (σ : Measure X) (q : NNReal → X × X → ENNReal)
    (hdensity : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x = σ.withDensity (fun y => q ε (x, y)))
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε) ∧ β < scale j * (outputs.eigenvalue ε).re ∧
      ∀ sf : HasStrongFellerKernel (C ε), ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ)
          (chain (C ε) (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
          (strongFeller (C ε) sf (stratum T A Λ ℓ N D i)
            (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ K * β ^ n := by
  have hdom : Tendsto (fun ε : NNReal => scale j * (outputs.eigenvalue ε).re)
      (𝓝 0) (𝓝 (Real.exp dominantPressure)) := by
    have h := (Complex.continuous_re.tendsto (det.rate : ℂ)).comp outputs.eigenvalue_convergence |>.const_mul (scale j)
    simpa only [Function.comp_apply, Complex.ofReal_re, hpressure] using h
  exact EventualProducedModelFiltrationGrowth.eventually_actual_stratum_bounds_from_produced_models
    T A Λ ℓ N D hA hΛ E Mid Weak J pressure dominantPressure hgap iH iW law prob
    generator scale models essential hKL hdet hprincipal
    (fun ε => scale j * (outputs.eigenvalue ε).re) hdom C hSF rawScale hUltra hFredholm
    hcompare σ q hdensity hpre hnull

end ConditionedStochasticStabilityHyperbolic.Global.EventualDominantPressureGrowth
