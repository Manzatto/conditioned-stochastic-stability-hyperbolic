module

public import AbsorbingMarkovChains.SpectralPowerBound
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
public import Mathlib.Order.Filter.Finite
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Pressure slack and nonmixing subordinate layer growth

Finite pressure separation and general spectral confinement supply one common
raw growth rate below the dominant eigenvalue. Gelfand's formula supplies all
subordinate power bounds without simple eigenvalues, rank-one projections or
mixing. The actual complex killed operator controls the actual real operator
through the isometric inclusion of real observables.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.PressureLayerBounds

/-- One strict raw pressure radius works for all finitely many subordinate
basic sets, including the case of no subordinate sets. -/
theorem exists_common_pressure_slack {I : Type*} (J : Finset I)
    (pressure : I → ℝ) (dominantPressure : ℝ)
    (hgap : ∀ i ∈ J, pressure i < dominantPressure) :
    ∃ r : ℝ, 0 < r ∧ r < Real.exp dominantPressure ∧ ∀ i ∈ J, Real.exp (pressure i) < r := by
  classical
  by_cases hJ : J.Nonempty
  · obtain ⟨i, hi, hmax⟩ := J.exists_max_image (fun i => Real.exp (pressure i)) hJ
    obtain ⟨r, hir, hr⟩ := exists_between (Real.exp_lt_exp.mpr (hgap i hi))
    exact ⟨r, (Real.exp_pos _).trans hir, hr, fun j hj => (hmax j hj).trans_lt hir⟩
  · refine ⟨Real.exp dominantPressure / 2, by positivity, ?_, ?_⟩
    · linarith [Real.exp_pos dominantPressure]
    · intro i hi
      exact False.elim (hJ ⟨i, hi⟩)

/-- General KL spectral confinement and dominant leading-rate convergence
produce common finite-layer power bounds. Periodic subordinate spectra are
allowed; none of their local operators needs a rank-one gap. -/
theorem eventually_subordinate_power_bounds
    {I Z : Type*} (A : I → Type*) [∀ i, NormedRing (A i)]
    [∀ i, NormedAlgebra ℂ (A i)] [∀ i, CompleteSpace (A i)]
    (J : Finset I) (pressure : I → ℝ) (dominantPressure : ℝ)
    (hgap : ∀ i ∈ J, pressure i < dominantPressure)
    (l : Filter Z) (operator : ∀ _z : Z, ∀ i : I, A i) (dominantRate : Z → ℝ)
    (hdom : Tendsto dominantRate l (𝓝 (Real.exp dominantPressure)))
    (hconf : ∀ i ∈ J, ∀ r : ℝ, Real.exp (pressure i) < r →
      ∀ᶠ z in l, spectralRadius ℂ (operator z i) < ENNReal.ofReal r) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ z in l, r < dominantRate z ∧
      ∀ i ∈ J, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖operator z i ^ n‖ ≤ C * r ^ n := by
  obtain ⟨r, hr, hrdom, hri⟩ := exists_common_pressure_slack J pressure dominantPressure hgap
  have hdomrate : ∀ᶠ z in l, r < dominantRate z := hdom.eventually (lt_mem_nhds hrdom)
  have hs : ∀ᶠ z in l, ∀ i ∈ J, spectralRadius ℂ (operator z i) < ENNReal.ofReal r :=
    (J.eventually_all).mpr (fun i hi => hconf i hi r (hri i hi))
  refine ⟨r, hr, ?_⟩
  filter_upwards [hdomrate, hs] with z hz hspec
  refine ⟨hz, ?_⟩
  intro i hi
  obtain ⟨q, hq, hqr, C, hC, hbound⟩ :=
    AbsorbingMarkovChains.SpectralPowerBound.exists_geometric_bound (operator z i) hr (hspec i hi)
  exact ⟨C, hC, fun n => (hbound n).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hq.le hqr.le n) hC)⟩

private theorem complex_operator_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ T < ENNReal.ofReal r) :
    ∃ q : ℝ, 0 < q ∧ q < r ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ K * q ^ n :=
  AbsorbingMarkovChains.SpectralPowerBound.exists_geometric_bound T hr hspec

section RealComplex

open ComplexStrongFeller

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

/-- The real observable inclusion is isometric in the actual sup norm. -/
def realInclusion : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℂ) := Complex.ofRealCLM.compLeftContinuousBounded X

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem realInclusion_norm (f : X →ᵇ ℝ) : ‖realInclusion f‖ = ‖f‖ := by
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm]
  congr 1
  funext x
  exact Complex.norm_real (f x)

theorem realInclusion_transfer (f : X →ᵇ ℝ) :
    realInclusion (transferOperator (𝕜 := ℝ) C hSF f) =
      transferOperator (𝕜 := ℂ) C hSF (realInclusion f) := by
  ext x
  change ((∫ y, f y ∂C.killedTransition x : ℝ) : ℂ) =
    ∫ y, (f y : ℂ) ∂C.killedTransition x
  exact integral_ofReal.symm

/-- Every raw power of the actual real transfer is bounded by the norm of
the corresponding raw complex transfer power. -/
theorem real_power_norm_le_complex (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) C hSF) ^ n‖ ≤
      ‖(b • transferOperator (𝕜 := ℂ) C hSF) ^ n‖ := by
  have hi (n : ℕ) (f : X →ᵇ ℝ) :
      realInclusion (((b • transferOperator (𝕜 := ℝ) C hSF) ^ n) f) =
        ((b • transferOperator (𝕜 := ℂ) C hSF) ^ n) (realInclusion f) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, smul_apply, smul_apply,
          map_smul, realInclusion_transfer C hSF, ih]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  calc
    _ = ‖realInclusion (((b • transferOperator (𝕜 := ℝ) C hSF) ^ n) f)‖ := (realInclusion_norm _).symm
    _ = ‖((b • transferOperator (𝕜 := ℂ) C hSF) ^ n) (realInclusion f)‖ := congrArg norm (hi n f)
    _ ≤ ‖(b • transferOperator (𝕜 := ℂ) C hSF) ^ n‖ * ‖realInclusion f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [realInclusion_norm]

set_option maxHeartbeats 800000 in
/-- Strict complex spectral-radius slack gives actual real-transfer power
bounds, with no real-spectrum or subordinate mixing assumption. -/
theorem exists_real_power_bound_of_complex_radius (b : ℝ) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ (b • transferOperator (𝕜 := ℂ) C hSF) < ENNReal.ofReal r) :
    ∃ q : ℝ, 0 < q ∧ q < r ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : ℕ, ‖(b • transferOperator (𝕜 := ℝ) C hSF) ^ n‖ ≤ K * q ^ n := by
  obtain ⟨q, hq, hqr, K, hK, hbound⟩ :=
    complex_operator_growth (b • transferOperator (𝕜 := ℂ) C hSF) hr hspec
  exact ⟨q, hq, hqr, K, hK, fun n => (real_power_norm_le_complex C hSF b n).trans (hbound n)⟩

/-- The complete actual subordinate producer: complex closed-layer radius
slack and a reference-null boundary give real Borel-stratum power bounds.
This bridges periodic/nonmixing local spectra to the actual global layers. -/
theorem exists_stratum_bound_of_complex_radius_and_density
    (U : Set X) (hU : MeasurableSet U) (b : ℝ)
    (σ : Measure X) (q : X × X → ENNReal)
    (htransition : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y)))
    (hnull : σ Uᶜ = 0) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ (b • transferOperator (𝕜 := ℂ) C hSF) < ENNReal.ofReal r) :
    ∃ β : ℝ, 0 < β ∧ β < r ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ) (RestrictedLayerChain.chain C U hU)
        (RestrictedLayerChain.strongFeller C hSF U hU)) ^ n‖ ≤ K * β ^ n := by
  obtain ⟨β, hβ, hβr, a, ha, hbound⟩ := exists_real_power_bound_of_complex_radius C hSF b hr hspec
  obtain ⟨K, hK, hstratum⟩ := NullBoundaryLayer.exists_stratum_power_bound_of_density
    (𝕜 := ℝ) C hSF U hU b σ q htransition hnull ha hβ hbound
  exact ⟨β, hβ, hβr, K, hK, hstratum⟩

end RealComplex

end ConditionedStochasticStabilityHyperbolic.Global.PressureLayerBounds
