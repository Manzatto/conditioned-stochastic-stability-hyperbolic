module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniMeasureStability
public import ConditionedStochasticStabilityHyperbolic.Spectral.PhysicalProjectorPairing
public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularCoreApproximation

/-! # Physical weak stability from KL and common regular-noise realizations

The source packet records actual retained kernels, their spectral pairings,
whole-smooth-core Riesz projector compatibility, and realization of the noisy
right function in a common regular range. Its multiplier laws hold on the
entire regular space. It contains no observable product integral or measure
convergence assertion. Those follow from the checked harmonic restriction,
common-core approximation, and the two KL projector applications.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniPhysicalStability

open Restriction KellerLiverani1999 KellerLiveraniMeasureStability

variable {S H W V Z Reg Core X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Explicit physical and cited regular-range source data. The finite
regularity margins are retained, with an intermediate order strictly below
`r-1`, so smooth approximation does not require smooth noisy eigenvectors. -/
structure PhysicalInputs (Pa : H →L[ℂ] H) (γ : H) (ν : ProbabilityMeasure X)
    (A : Set (X →ᵇ ℝ)) (M : A → H →L[ℂ] H) where
  original : AbsorbingMarkovChains.CanonicalChain X
  cutoff : AbsorbingMarkovChains.CanonicalChain X
  originalSF : HasStrongFellerKernel original
  cutoffSF : HasStrongFellerKernel cutoff
  retained : Set X
  badOriginal : Set X
  badCutoff : Set X
  retainedMeasurable : MeasurableSet retained
  noReturnOriginal : ∀ x : retained, ∀ᵐ y ∂original.killedTransition x.val,
    y ∉ retained → y ∈ badOriginal
  extinctOriginal : ∀ x ∈ badOriginal, ∃ n : ℕ,
    original.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  noReturnCutoff : ∀ x : retained, ∀ᵐ y ∂cutoff.killedTransition x.val,
    y ∉ retained → y ∈ badCutoff
  extinctCutoff : ∀ x ∈ badCutoff, ∃ n : ℕ,
    cutoff.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  retainedKernelEq : LeanShared.SubtypeKernel.restrict original.killedTransition
    retained retainedMeasurable = LeanShared.SubtypeKernel.restrict cutoff.killedTransition
    retained retainedMeasurable
  originalData : RankOneSpectralData
    (ComplexStrongFeller.transferOperator (𝕜 := ℝ) original originalSF) (1 : X →ᵇ ℝ)
  cutoffData : RankOneSpectralData
    (ComplexStrongFeller.transferOperator (𝕜 := ℝ) cutoff cutoffSF) (1 : X →ᵇ ℝ)
  rates : originalData.rate = cutoffData.rate
  retainedScalar : ℝ
  retainedScalar_ne : retainedScalar ≠ 0
  retainedVectors : restrictObservable retained originalData.eigenvector =
    retainedScalar • restrictObservable retained cutoffData.eigenvector
  retainedVector_ne : restrictObservable retained cutoffData.eigenvector ≠ 0
  originalLeftMeasure : Measure X
  originalLeftRep : ∀ f : X →ᵇ ℝ, originalData.mean f = ∫ x, f x ∂originalLeftMeasure
  probabilityProduct : (ν : Measure X) =
    LeanShared.eigenvectorMeasure originalLeftMeasure originalData.eigenvector
  cutoffLeft : (X →ᵇ ℂ) →L[ℂ] ℂ
  cutoffLeft_real : ∀ f, cutoffLeft (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
    (cutoffData.mean f : ℂ)
  cutoffProjector : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)
  cutoffProjector_rankOne : cutoffProjector =
    cutoffLeft.smulRight (AbsorbingMarkovChains.ComplexKernel.ofReal cutoffData.eigenvector)
  analyticAmbient : H →L[ℂ] Z
  physicalAmbient : (X →ᵇ ℂ) →L[ℂ] Z
  regularity : ℝ
  positiveExponent : ℝ
  negativeExponent : ℝ
  regularOrder : ℝ
  margins : RegularCoreApproximation.RegularityMargins regularity positiveExponent
    negativeExponent regularOrder
  realization : RegularCoreApproximation.Realization (Reg := Reg) (A := H)
    (Core := Core) (X := X)
  projectorCore : ∀ u : Core,
    physicalAmbient (cutoffProjector (realization.physical (realization.smooth u))) =
    analyticAmbient (Pa (realization.analytic (realization.smooth u)))
  analyticScalar : ℂ
  analyticScalar_ne : analyticScalar ≠ 0
  ambientVectors : physicalAmbient
    (AbsorbingMarkovChains.ComplexKernel.ofReal cutoffData.eigenvector) =
    analyticScalar • analyticAmbient γ
  analyticVector_ne : analyticAmbient γ ≠ 0
  regularVector : Reg
  regularVector_physical : realization.physical regularVector =
    AbsorbingMarkovChains.ComplexKernel.ofReal cutoffData.eigenvector
  regularVector_analytic : realization.analytic regularVector = analyticScalar • γ
  regularMultiplier : A → Reg →L[ℂ] Reg
  multiplier_physical : ∀ h : A, ∀ v : Reg,
    realization.physical (regularMultiplier h v) = realization.physical v *
      AbsorbingMarkovChains.ComplexKernel.ofReal h.val
  multiplier_analytic : ∀ h : A, realization.analytic.comp (regularMultiplier h) =
    (M h).comp realization.analytic

/-- The source packet produces the integration representation. -/
theorem PhysicalInputs.integral_eq
    {Pa : H →L[ℂ] H} {γ : H} {ν : ProbabilityMeasure X}
    {A : Set (X →ᵇ ℝ)} {M : A → H →L[ℂ] H}
    (I : PhysicalInputs (Z := Z) (Reg := Reg) (Core := Core) Pa γ ν A M)
    (ma : H →L[ℂ] ℂ) (hPa : Pa = ma.smulRight γ) (h : A) :
    (∫ x, h.val x ∂(ν : Measure X)) = (ma (M h γ)).re := by
  obtain ⟨u, hup, hua⟩ := RegularCoreApproximation.exists_product_approximants
    I.realization (I.regularMultiplier h) (M h) h.val (I.multiplier_physical h)
    (I.multiplier_analytic h) I.regularVector I.cutoffData.eigenvector γ I.analyticScalar
    I.regularVector_physical I.regularVector_analytic
  rw [I.probabilityProduct]
  exact PhysicalProjectorPairing.integral_eq_analytic_product
    I.original I.cutoff I.originalSF I.cutoffSF I.retained I.badOriginal I.badCutoff
    I.retainedMeasurable I.noReturnOriginal I.extinctOriginal I.noReturnCutoff
    I.extinctCutoff I.retainedKernelEq I.originalData I.cutoffData I.rates
    I.retainedScalar I.retainedScalar_ne I.retainedVectors I.retainedVector_ne
    I.originalLeftMeasure I.originalLeftRep I.cutoffLeft I.cutoffLeft_real Pa
    I.cutoffProjector γ ma hPa I.cutoffProjector_rankOne I.analyticAmbient I.physicalAmbient
    (fun u => I.realization.analytic (I.realization.smooth u))
    (fun u => I.realization.physical (I.realization.smooth u)) I.projectorCore
    I.analyticScalar I.analyticScalar_ne I.ambientVectors I.analyticVector_ne
    h.val ((M h).restrictScalars ℝ) u hup hua

/-- Two actual KL applications and physical source realizations imply weak
convergence of the actual original-weight product probabilities. Neither
observable integration identities nor dual convergence are supplied. -/
theorem tendsto_actual_probability_of_physical_sources
    {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
    {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] V}
    {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
    {qs δs qm δm : ℝ}
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hi : IsCompactOperator i) (hj : Function.Injective j) (hdense : DenseRange i)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0)
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H)
    (ν : ℝ≥0 → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hsources : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), Nonempty
      (PhysicalInputs (Z := Z) (Reg := Reg) (Core := Core)
        (om.projection ε) (rightBranch os i ε) (ν ε) A M))
    (hequilibrium : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure X)) =
      realLeftTrace os om φ 0 (M h (i ds.vector))) :
    Tendsto ν (𝓝 (0 : ℝ≥0)) (𝓝 ν₀) := by
  apply tendsto_probability_of_two_projector_applications os om hi hj hdense hagree
    φ hφ A hA (fun h => (M h).restrictScalars ℝ) ν ν₀ _ hequilibrium
  intro h
  filter_upwards [hsources, eventually_projector_eq_leftTrace os om hagree φ hφ]
    with ε hsource hprojector
  obtain ⟨I⟩ := hsource
  exact I.integral_eq (leftTrace os om φ ε) hprojector h

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniPhysicalStability
