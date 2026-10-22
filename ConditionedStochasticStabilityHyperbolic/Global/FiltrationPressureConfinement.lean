module

public import ConditionedStochasticStabilityHyperbolic.Global.FinitePressureConfinement
public import ConditionedStochasticStabilityHyperbolic.Global.ClosedLayerReference
public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel

/-!
# Finite pressure/KL bounds for the actual shifted filtration strata

The kernels, references, densities and null complements are constructed from
one actual full noisy chain and the proved shifted adapted geometry. The
output concerns direct ambient stratum kernels, not arbitrary supplied local
models. No mixing assumption is made on subordinate analytic operators.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
open LeanShared ShiftedFiltrationGeometry ShiftedBoundaryGeometry ClosedLayerReference
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel FinitePressureConfinement
open KellerLiverani1999
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

def stratum (i : Fin ℓ) : Set X := filtrationLayer (levels T A Λ ℓ N D) i.val

def closedLayer (i : Fin ℓ) : Set X := closure (stratum T A Λ ℓ N D i)

theorem closedLayer_measurable (i : Fin ℓ) : MeasurableSet (closedLayer T A Λ ℓ N D i) :=
  isClosed_closure.measurableSet

theorem stratum_measurable (hA : IsOpen A) (i : Fin ℓ) : MeasurableSet (stratum T A Λ ℓ N D i) := by
  have hupper := (levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)).isClosed.measurableSet
  by_cases hi : i.val = 0
  · change MeasurableSet (levels T A Λ ℓ N D (i.val + 1) \ levels T A Λ ℓ N D i.val)
    rw [hi, levels_zero]
    simpa only [hi] using hupper.diff hA.measurableSet
  · exact hupper.diff (levels_positive_compact T A Λ ℓ N D i.val
      (Nat.pos_of_ne_zero hi) (by omega)).isClosed.measurableSet

/-- The full actual analytic-to-stratum pressure producer. Only cited
KL/confinement/cross-space spectral sources and deterministic pressure
bounds are inputs; actual closed-layer density and nullity are derived. -/
theorem eventually_actual_filtration_stratum_bounds
    (hA : IsOpen A)
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
    (hSF : ∀ ε, HasStrongFellerKernel (C ε)) (rawScale : Fin ℓ → ℝ)
    (hcompare : ∀ i ∈ J, ∀ ε, spectralRadius ℂ (rawScale i • transferOperator (𝕜 := ℂ)
      (chain (C ε) (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))
      (strongFeller (C ε) (hSF ε) (closedLayer T A Λ ℓ N D i)
        (closedLayer_measurable T A Λ ℓ N D i))) ≤ spectralRadius ℂ ((scale i : ℂ) • P i ε))
    (σ : Measure X) (q : NNReal → X × X → ENNReal)
    (hdensity : ∀ ε x, (C ε).killedTransition x = σ.withDensity (fun y => q ε (x, y)))
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε : NNReal in 𝓝 0, β < dominantRate ε ∧
      ∀ i ∈ J, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ‖(rawScale i • transferOperator (𝕜 := ℝ)
          (chain (C ε) (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
          (strongFeller (C ε) (hSF ε) (stratum T A Λ ℓ N D i)
            (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ K * β ^ n := by
  let K := closedLayer T A Λ ℓ N D
  let S := stratum T A Λ ℓ N D
  let CK := fun i ε => chain (C ε) (K i) (closedLayer_measurable T A Λ ℓ N D i)
  let sfK := fun i ε => strongFeller (C ε) (hSF ε) (K i) (closedLayer_measurable T A Λ ℓ N D i)
  let U := fun i => (Subtype.val : K i → X) ⁻¹' S i
  have hU : ∀ i, MeasurableSet (U i) := fun i =>
    (stratum_measurable T A Λ ℓ N D hA i).preimage measurable_subtype_coe
  have hlocalDensity : ∀ i ∈ J, ∀ ε x, (CK i ε).killedTransition x =
      (σ.comap (Subtype.val : K i → X)).withDensity (fun y => q ε (x.val, y.val)) := by
    intro i _hi ε
    exact restricted_density_law (C ε) (K i) (closedLayer_measurable T A Λ ℓ N D i) σ (q ε) (hdensity ε)
  have hlocalNull : ∀ i ∈ J, (σ.comap (Subtype.val : K i → X)) (U i)ᶜ = 0 := by
    intro i _hi
    exact relative_stratum_complement_zero σ (S i) (K i) (closedLayer_measurable T A Λ ℓ N D i)
      (closed_layer_extra_zero T A hA Λ ℓ N D σ hpre hnull i)
  obtain ⟨β, hβ, hevent⟩ := eventually_actual_stratum_bounds_from_finite_KL E Weak
    (fun i => K i) J (fun i => pressure (D.index i)) dominantPressure hgap
    P embed hyp hKL scale hscale hdet hessential dominantRate hdom CK sfK rawScale hcompare
    U hU (fun i => σ.comap (Subtype.val : K i → X))
    (fun i ε x => q ε (x.1.val, x.2.val)) hlocalDensity hlocalNull
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hevent] with ε hε
  refine ⟨hε.1, ?_⟩
  intro i hi
  obtain ⟨B, hB, hpow⟩ := hε.2 i hi
  refine ⟨B, hB, ?_⟩
  intro n
  have he := nested_power_norm_eq (𝕜 := ℝ) (S i) (K i) subset_closure (C ε) (hSF ε)
    (stratum_measurable T A Λ ℓ N D hA i) (closedLayer_measurable T A Λ ℓ N D i) (rawScale i) n
  exact he ▸ hpow n

end ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
