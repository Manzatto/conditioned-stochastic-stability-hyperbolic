module

public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
public import ConditionedStochasticStabilityHyperbolic.Global.EventualNoiseEigenPressureGrowth

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
namespace ConditionedStochasticStabilityHyperbolic.Global.EventualActualFiltrationGrowth
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry ClosedLayerReference
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel FiltrationPressureConfinement
open KellerLiverani1999
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

local instance compactClosedLayer (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

theorem eventually_actual_stratum_bounds_from_eigen_sources
    (hA : IsOpen A)
    (hΛ : ∀ i : Fin ℓ, (Λ (D.index i)).Nonempty)
    (E Weak : Fin ℓ → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
    [∀ i, NormedAddCommGroup (Weak i)] [∀ i, NormedSpace ℂ (Weak i)]
    (J : Finset (Fin ℓ)) (pressure : I → ℝ) (dominantPressure : ℝ)
    (hgap : ∀ i ∈ J, pressure (D.index i) < dominantPressure)
    (P : ∀ i, NNReal → (E i) →L[ℂ] (E i))
    (embed : ∀ i, (E i) →L[ℂ] (Weak i))
    (hyp : ∀ i, Hypotheses (P i) (embed i))
    (hKL : ∀ i ∈ J, ClassicalConfinementContract (E := E i) (W := Weak i))
    (scale : Fin ℓ → ℝ) (hscale : ∀ i ∈ J, 0 < scale i)
    (hdet : ∀ i ∈ J, spectralRadius ℂ ((scale i : ℂ) • P i 0) ≤
      ENNReal.ofReal (Real.exp (pressure (D.index i))))
    (hessential : ∀ i ∈ J, scale i * (hyp i).alpha ≤ Real.exp (pressure (D.index i)))
    (dominantRate : NNReal → ℝ)
    (hdom : Tendsto dominantRate (𝓝 0) (𝓝 (Real.exp dominantPressure)))
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
      scale i * (hyp i).alpha < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • P i ε))
    (σ : Measure X) (q : NNReal → X × X → ENNReal)
    (hdensity : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x = σ.withDensity (fun y => q ε (x, y)))
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε) ∧ β < dominantRate ε ∧
      ∀ sf : HasStrongFellerKernel (C ε), ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ)
          (chain (C ε) (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
          (strongFeller (C ε) sf (stratum T A Λ ℓ N D i)
            (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ K * β ^ n := by
  let K := closedLayer T A Λ ℓ N D
  let S := stratum T A Λ ℓ N D
  let CK := fun i ε => chain (C ε) (K i) (closedLayer_measurable T A Λ ℓ N D i)
  let U := fun i => (Subtype.val : K i → X) ⁻¹' S i
  have hU : ∀ i, MeasurableSet (U i) := fun i =>
    (stratum_measurable T A Λ ℓ N D hA i).preimage measurable_subtype_coe
  have hlocalSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ i ∈ J, HasStrongFellerKernel (CK i ε) := by
    filter_upwards [hSF] with ε sf
    exact fun i _ => strongFeller (C ε) sf (K i) (closedLayer_measurable T A Λ ℓ N D i)
  have hlocalDensity : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ i ∈ J, ∀ x, (CK i ε).killedTransition x =
      (σ.comap (Subtype.val : K i → X)).withDensity (fun y => q ε (x.val, y.val)) := by
    filter_upwards [hdensity] with ε hε
    exact fun i _ => restricted_density_law (C ε) (K i)
      (closedLayer_measurable T A Λ ℓ N D i) σ (q ε) hε
  have hlocalCompare : ∀ i ∈ J, ∀ᶠ ε : NNReal in 𝓝[>] 0,
      ∀ (sf : HasStrongFellerKernel (CK i ε)) (f : K i →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (rawScale i • transferOperator (𝕜 := ℂ) (CK i ε) sf) f = z • f →
      scale i * (hyp i).alpha < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • P i ε) := by
    intro i hi
    filter_upwards [hSF, hcompare i hi] with ε sf hc
    intro _ f hf z he hz
    exact hc sf f hf z he hz
  have hlocalNull : ∀ i ∈ J, (σ.comap (Subtype.val : K i → X)) (U i)ᶜ = 0 := by
    intro i _hi
    exact relative_stratum_complement_zero σ (S i) (K i) (closedLayer_measurable T A Λ ℓ N D i)
      (closed_layer_extra_zero T A hA Λ ℓ N D σ hpre hnull i)
  let : ∀ i : Fin ℓ, Nonempty (K i) := fun i => by
    obtain ⟨x, hx⟩ := hΛ i
    have hcore := (closed_layer_core T A Λ ℓ N D hA i).symm ▸ hx
    exact ⟨⟨x, LeanShared.forwardTrapped_subset T _ hcore.1⟩⟩
  obtain ⟨β, hβ, hevent⟩ := EventualNoiseEigenPressureGrowth.eventually_stratum_bounds_from_KL_and_eigen_comparison E Weak
    (fun i => K i) J (fun i => pressure (D.index i)) dominantPressure hgap
    P embed hyp hKL scale hscale hdet hessential dominantRate hdom CK hlocalSF rawScale hUltra hFredholm hlocalCompare
    U hU (fun i => σ.comap (Subtype.val : K i → X))
    (fun i ε x => q ε (x.1.val, x.2.val)) hlocalDensity hlocalNull
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hevent, hSF] with ε heventε sf₀
  refine ⟨sf₀, heventε.1, ?_⟩
  intro sf i hi
  obtain ⟨B, hB, hpow⟩ := (heventε.2 i hi).2
    (strongFeller (C ε) sf (K i) (closedLayer_measurable T A Λ ℓ N D i))
  refine ⟨B, hB, ?_⟩
  intro n
  have he := nested_power_norm_eq (𝕜 := ℝ) (S i) (K i) subset_closure (C ε) sf
    (stratum_measurable T A Λ ℓ N D hA i) (closedLayer_measurable T A Λ ℓ N D i) (rawScale i) n
  exact he ▸ hpow n

end ConditionedStochasticStabilityHyperbolic.Global.EventualActualFiltrationGrowth
