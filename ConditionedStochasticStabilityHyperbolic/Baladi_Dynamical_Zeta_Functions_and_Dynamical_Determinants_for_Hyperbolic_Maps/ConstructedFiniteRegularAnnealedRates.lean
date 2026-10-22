module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorWindowRestriction
public import LeanShared.Analysis.ActualFiniteRegularAnnealedPerturbation
public import LeanShared.Analysis.ConstructedCommonCoreApproximation

/-!
# Exact rates of constructed finite-regular Keller--Liverani inputs

The constructor retains its principal and weak growth constants in its
conclusion. These are outputs, so the physical pressure gap can be applied
to the chosen witness without assuming an additional rate identity.

The generator is the actual weighted-function transfer. Common regular
approximation derives the weak one-step equation. Dense smooth-core
continuity gives evaluated-vector Bochner measurability, and compact
input inclusion yields mixed-norm convergence of varying-law averages.
The block is a proved tuple estimate from ManifoldIntrinsicBlock, not a
deferred classical conclusion. Globally bounded generator sources may use
a common small generator domain or the clipped noise family.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ConditionedStochasticStabilityHyperbolic.ConstructedFiniteRegularAnnealedRates

open LeanShared LeanShared.DyadicCompletion LeanShared.FiniteRegularTransferRealization
open LeanShared.AnnealedOperatorBounds
open KellerLiverani1999

theorem exists_inputs
    {X G Ω Core VS VH VW High Low : Type*}
    [MetricSpace G] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    [AddCommGroup Core] [Module ℂ Core]
    [NormedAddCommGroup VS] [NormedSpace ℂ VS] [CompleteSpace VS]
    [NormedAddCommGroup VH] [NormedSpace ℂ VH]
    [NormedAddCommGroup VW] [NormedSpace ℂ VW] [CompleteSpace VW]
    [NormedAddCommGroup High] [NormedSpace ℂ High]
    [NormedAddCommGroup Low] [NormedSpace ℂ Low]
    (qS : Core →ₗ[ℂ] VS) (qH : Core →ₗ[ℂ] VH) (qW : Core →ₗ[ℂ] VW)
    (smooth : Core →ₗ[ℂ] (X → ℂ))
    (viewHigh : High →ₗ[ℂ] (X → ℂ)) (hinjHigh : Function.Injective viewHigh)
    (viewLow : Low →ₗ[ℂ] (X → ℂ)) (hinjLow : Function.Injective viewLow)
    (downgrade : High →L[ℂ] Low) (hview : ∀ f, viewLow (downgrade f) = viewHigh f)
    (F : G → X → X) (g : X → ℝ)
    (hhigh : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewHigh.range)
    (hlow : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewLow.range)
    (realizeStrong : High →L[ℂ] closedCore qS) (realizeWeak : Low →L[ℂ] closedCore qW)
    (i : closedCore qS →L[ℂ] closedCore qH) (hicompact : IsCompactOperator i)
    (j : closedCore qS →L[ℂ] closedCore qW)
    (hi : ∀ c, i (coreLift qS c) = coreLift qH c)
    (hj : ∀ c, j (coreLift qS c) = coreLift qW c)
    (approximation : High → ℕ → Core)
    (happroxStrong : ∀ f, Tendsto (fun n => coreLift qS (approximation f n)) atTop (𝓝 (realizeStrong f)))
    (happroxWeak : ∀ f, Tendsto (fun n => coreLift qW (approximation f n)) atTop
      (𝓝 (realizeWeak (downgrade f))))
    (LS LW : ℝ) (hLS : 0 ≤ LS) (hLW : 0 ≤ LW)
    (hstrong : ∀ a c, ‖targetCore qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a c‖ ≤ LS * ‖qS c‖)
    (hweak : ∀ a c,
      ‖FiniteRegularTransferBetweenSpaces.targetCore smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤ LW * ‖qH c‖)
    (T : G)
    (hlowCore : ∀ c, Tendsto (fun a => regularAction smooth Low viewLow hinjLow F g hlow a c)
      (𝓝 T) (𝓝 (regularAction smooth Low viewLow hinjLow F g hlow T c))) (noise : ℝ≥0 → Ω → G) (noiseConstant : ℝ)
    (hclose : ∀ ε ω, dist (noise ε ω) T ≤ noiseConstant * (ε : ℝ))
    (μ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (μ ε)]
    (hnoiseCore : ∀ ε c, Continuous (fun ω =>
      regularAction smooth High viewHigh hinjHigh F g hhigh (noise ε ω) c))
    (LWstep : ℝ) (hLWstep : 0 ≤ LWstep)
    (hweakStepCore : ∀ a c,
      ‖targetCore qW smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤ LWstep * ‖qW c‖)
    (N : ℕ) (hN : 0 < N) (ρ weakRate scale : ℝ)
    (hρ : 0 < ρ) (hrate : ρ < weakRate) (hweakRate : LWstep ≤ weakRate)
    (hscale : 1 ≤ scale) (hρscale : ρ < scale)
    (U : Set G) (hU : U ∈ 𝓝 T) (B : ℝ) (hB : 0 ≤ B)
    (block : ∀ word : Fin N → G, (∀ k, word k ∈ U) → ∀ x,
      ‖FiniteBlockAnnealedEstimates.listWord
        (operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh) (List.ofFn word) x‖ ≤
        ρ ^ N * ‖x‖ + B * ‖j x‖) :
    ∃ inputs : KellerLiverani1999.ActualAnnealedInputs μ (fun ε => (inferInstance : IsProbabilityMeasure (μ ε))) j scale,
      (∀ ε ω, inputs.generator ε ω =
        operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh (noise ε ω)) ∧
      inputs.principal = ρ ∧ inputs.weakRate = weakRate ∧
      inputs.weakOneStep = LWstep ∧ inputs.operatorBound = LS := by
  let PS := operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh
  have hbound : ∀ ε ω, ‖PS (noise ε ω)‖ ≤ LS := fun ε ω =>
    operator_norm_le qS smooth High viewHigh hinjHigh realizeStrong F g hhigh LS hstrong hLS _
  have hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => PS (noise ε ω) x) (μ ε) := by
    intro ε x
    apply DenseCoreRandomOperators.aestronglyMeasurable_of_continuous_core
      (μ ε) _ (coreLift qS) (coreLift_dense qS) _ x
    intro c
    exact (realizeStrong.continuous.comp (hnoiseCore ε c)).congr
      (fun ω => (operator_core qS smooth High viewHigh hinjHigh realizeStrong F g hhigh LS hstrong (noise ε ω) c).symm)
  have hcompat := CommonFiniteRegularTransferCompatibility.operator_compatibility
    qS qW qW smooth viewHigh hinjHigh viewLow hinjLow downgrade hview F g hhigh hlow
    realizeStrong realizeWeak j j hj hj approximation happroxStrong happroxWeak LS LWstep
    hstrong hweakStepCore
  let PW := FiniteRegularTransferBetweenSpaces.operator qW smooth Low viewLow hinjLow realizeWeak F g hlow
  have hPW : ∀ a, ‖PW a‖ ≤ LWstep := fun a =>
    FiniteRegularTransferBetweenSpaces.operator_norm_le qW smooth Low viewLow hinjLow
      realizeWeak F g hlow LWstep hweakStepCore hLWstep a
  have hweakCompleted : ∀ a x, ‖j (PS a x)‖ ≤ LWstep * ‖j x‖ := by
    intro a x
    have he : PW a (j x) = j (PS a x) := congrArg (fun A => A x) (hcompat a)
    rw [← he]
    exact ((PW a).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hPW a) (norm_nonneg _))
  obtain ⟨window, hwindow, hwindowNoise⟩ :=
    KellerLiverani1999.exists_positive_window_of_eventually
      (CompactAnnealedPerturbation.common_neighborhood_of_uniform_distance T noise noiseConstant hclose U hU)
  let AR := FiniteRegularTransferBetweenSpaces.operator qH smooth Low viewLow hinjLow realizeWeak F g hlow
  have hrectCompat := CommonFiniteRegularTransferCompatibility.operator_compatibility
    qS qH qW smooth viewHigh hinjHigh viewLow hinjLow downgrade hview F g hhigh hlow
    realizeStrong realizeWeak i j hi hj approximation happroxStrong happroxWeak LS LW hstrong hweak
  have hrectBound : ∀ a, ‖AR a‖ ≤ LW := fun a =>
    FiniteRegularTransferBetweenSpaces.operator_norm_le qH smooth Low viewLow hinjLow realizeWeak F g hlow LW hweak hLW a
  have hcore : ∀ c, Tendsto (fun a => AR a (coreLift qH c)) (𝓝 T)
      (𝓝 (AR T (coreLift qH c))) := by
    intro c
    simpa only [AR, Function.comp_def,
      FiniteRegularTransferBetweenSpaces.operator_core qH smooth Low viewLow hinjLow realizeWeak F g hlow LW hweak] using
      realizeWeak.continuous.tendsto (regularAction smooth Low viewLow hinjLow F g hlow T c) |>.comp (hlowCore c)
  let average := fun ε => pointwiseAnnealed (μ ε) (fun ω => PS (noise ε ω)) (hmeas ε) LS (hbound ε)
  have havg : ∀ ε x, average ε x = ∫ ω, PS (noise ε ω) x ∂μ ε :=
    fun ε x => pointwiseAnnealed_apply (μ ε) _ (hmeas ε) LS (hbound ε) x
  have hlimit : Tendsto (fun ε => ‖j.comp (average ε - PS T)‖) (𝓝 0) (𝓝 0) :=
    CompactAnnealedPerturbation.mixed_norm_average_tendsto_zero i hicompact j AR PS T
      hrectCompat LW hLW (Eventually.of_forall hrectBound) (coreLift qH) (coreLift_dense qH) hcore
      noise (𝓝 0) (CompactAnnealedPerturbation.common_neighborhood_of_uniform_distance T noise noiseConstant hclose)
      μ hmeas (fun _ => LS) hbound
  have hnoiseZero : ∀ ω, noise 0 ω = T := by
    intro ω
    apply dist_le_zero.mp
    simpa using hclose 0 ω
  have hbase : average 0 = PS T := by
    apply ContinuousLinearMap.ext
    intro x
    rw [havg]
    simp only [hnoiseZero]
    simp [PS]
  let inputs : KellerLiverani1999.ActualAnnealedInputs μ (fun ε => (inferInstance : IsProbabilityMeasure (μ ε))) j scale := {
    generator := fun ε ω => PS (noise ε ω)
    measurable := hmeas
    window := window
    window_pos := hwindow
    blockLength := N
    blockLength_pos := hN
    principal := ρ
    weakRate := weakRate
    weakOneStep := LWstep
    operatorBound := LS
    remainder := B
    principal_pos := hρ
    principal_weak := hrate
    weakOneStep_nonneg := hLWstep
    weakOneStep_rate := hweakRate
    operatorBound_nonneg := hLS
    remainder_nonneg := hB
    scale_ge_one := hscale
    principal_scale := hρscale
    generator_bound := hbound
    weak_bound := fun _ _ ω x => hweakCompleted _ x
    block_bound := by
      intro ε hε word hlen x
      rw [FiniteBlockAnnealedEstimates.listWord_map]
      have ht := block (fun k => noise ε (word.get (Fin.cast hlen.symm k)))
        (fun k => hwindowNoise ε hε _) x
      convert ht using 1
      congr 2
      congr 1
      apply List.ext_get
      · simp [hlen]
      · intro n hn hm
        simp
    perturbation := by
      have heq : varyingNoiseOperator μ (fun ε => (inferInstance : IsProbabilityMeasure (μ ε)))
          (fun ε ω => PS (noise ε ω)) hmeas LS hbound = average := by
        funext ε
        apply ContinuousLinearMap.ext
        intro x
        exact (havg ε x).symm
      simpa only [heq, hbase] using hlimit }
  exact ⟨inputs, (fun _ _ => rfl), rfl, rfl, rfl, rfl⟩


/-- The simultaneous approximation premise is itself constructed from the
dense ordinary little-regularity core and the two actual core identities. -/
theorem exists_inputs_of_regular_density
    {X G Ω Core VS VH VW High Low : Type*}
    [MetricSpace G] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    [AddCommGroup Core] [Module ℂ Core]
    [NormedAddCommGroup VS] [NormedSpace ℂ VS] [CompleteSpace VS]
    [NormedAddCommGroup VH] [NormedSpace ℂ VH]
    [NormedAddCommGroup VW] [NormedSpace ℂ VW] [CompleteSpace VW]
    [NormedAddCommGroup High] [NormedSpace ℂ High]
    [NormedAddCommGroup Low] [NormedSpace ℂ Low]
    (qS : Core →ₗ[ℂ] VS) (qH : Core →ₗ[ℂ] VH) (qW : Core →ₗ[ℂ] VW)
    (smooth : Core →ₗ[ℂ] (X → ℂ))
    (viewHigh : High →ₗ[ℂ] (X → ℂ)) (hinjHigh : Function.Injective viewHigh)
    (viewLow : Low →ₗ[ℂ] (X → ℂ)) (hinjLow : Function.Injective viewLow)
    (downgrade : High →L[ℂ] Low) (hview : ∀ f, viewLow (downgrade f) = viewHigh f)
    (F : G → X → X) (g : X → ℝ)
    (hhigh : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewHigh.range)
    (hlow : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewLow.range)
    (realizeStrong : High →L[ℂ] closedCore qS) (realizeWeak : Low →L[ℂ] closedCore qW)
    (i : closedCore qS →L[ℂ] closedCore qH) (hicompact : IsCompactOperator i)
    (j : closedCore qS →L[ℂ] closedCore qW)
    (hi : ∀ c, i (coreLift qS c) = coreLift qH c)
    (hj : ∀ c, j (coreLift qS c) = coreLift qW c)
    (regularCore : Core →ₗ[ℂ] High) (regularDense : DenseRange regularCore)
    (realizeStrong_core : ∀ c, realizeStrong (regularCore c) = coreLift qS c)
    (realizeWeak_core : ∀ c, realizeWeak (downgrade (regularCore c)) = coreLift qW c)
    (LS LW : ℝ) (hLS : 0 ≤ LS) (hLW : 0 ≤ LW)
    (hstrong : ∀ a c, ‖targetCore qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a c‖ ≤ LS * ‖qS c‖)
    (hweak : ∀ a c,
      ‖FiniteRegularTransferBetweenSpaces.targetCore smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤ LW * ‖qH c‖)
    (T : G)
    (hlowCore : ∀ c, Tendsto (fun a => regularAction smooth Low viewLow hinjLow F g hlow a c)
      (𝓝 T) (𝓝 (regularAction smooth Low viewLow hinjLow F g hlow T c))) (noise : ℝ≥0 → Ω → G) (noiseConstant : ℝ)
    (hclose : ∀ ε ω, dist (noise ε ω) T ≤ noiseConstant * (ε : ℝ))
    (μ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (μ ε)]
    (hnoiseCore : ∀ ε c, Continuous (fun ω =>
      regularAction smooth High viewHigh hinjHigh F g hhigh (noise ε ω) c))
    (LWstep : ℝ) (hLWstep : 0 ≤ LWstep)
    (hweakStepCore : ∀ a c,
      ‖targetCore qW smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤ LWstep * ‖qW c‖)
    (N : ℕ) (hN : 0 < N) (ρ weakRate scale : ℝ)
    (hρ : 0 < ρ) (hrate : ρ < weakRate) (hweakRate : LWstep ≤ weakRate)
    (hscale : 1 ≤ scale) (hρscale : ρ < scale)
    (U : Set G) (hU : U ∈ 𝓝 T) (B : ℝ) (hB : 0 ≤ B)
    (block : ∀ word : Fin N → G, (∀ k, word k ∈ U) → ∀ x,
      ‖FiniteBlockAnnealedEstimates.listWord
        (operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh) (List.ofFn word) x‖ ≤
        ρ ^ N * ‖x‖ + B * ‖j x‖) :
    ∃ inputs : KellerLiverani1999.ActualAnnealedInputs μ (fun ε => (inferInstance : IsProbabilityMeasure (μ ε))) j scale,
      (∀ ε ω, inputs.generator ε ω =
        operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh (noise ε ω)) ∧
      inputs.principal = ρ ∧ inputs.weakRate = weakRate ∧
      inputs.weakOneStep = LWstep ∧ inputs.operatorBound = LS := by
  obtain ⟨approximation, happroxStrong, happroxWeak⟩ :=
    ConstructedCommonCoreApproximation.exists_simultaneous qS qW regularCore regularDense
      downgrade realizeStrong realizeWeak realizeStrong_core realizeWeak_core
  exact exists_inputs qS qH qW smooth viewHigh hinjHigh viewLow hinjLow downgrade hview
    F g hhigh hlow realizeStrong realizeWeak i hicompact j hi hj
    approximation happroxStrong happroxWeak LS LW hLS hLW hstrong hweak T hlowCore
    noise noiseConstant hclose μ hnoiseCore LWstep hLWstep hweakStepCore
    N hN ρ weakRate scale hρ hrate hweakRate hscale hρscale U hU B hB block

end ConditionedStochasticStabilityHyperbolic.ConstructedFiniteRegularAnnealedRates
