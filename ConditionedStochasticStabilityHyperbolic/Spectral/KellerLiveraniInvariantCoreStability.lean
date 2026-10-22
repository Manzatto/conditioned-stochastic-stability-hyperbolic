module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InvariantPhysicalPairing
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniRieszGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniPuncturedStability

/-! # Actual local weak stability through invariant finite-regular core powers

Both KL applications produce the analytic projector bounds, dual limits and
normalized powers. The actual physical real gap produces its complex power
limit. A common invariant finite-regular seed and literal multipliers produce
physical product pairings. Noise regularity is used only at positive scales;
the zero parameter requires only the deterministic equilibrium identification.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
open KellerLiverani1999

variable {S H W V : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
  {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] V}
  {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
  {qs δs qm δm : ℝ}

/-- Normalization of the actual weak trace is derived from the two agreeing
KL projectors, not supplied as an extra dual normalization premise. -/
theorem eventually_leftTrace_normalization
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), leftTrace os om φ ε (rightBranch os i ε) = 1 := by
  have hden := φ.continuous.continuousAt.tendsto.comp os.projected_vector_weak_convergence
  have hnz : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), φ (j (rightBranch os i ε)) ≠ 0 := hden.eventually_ne hφ
  have hwindow : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ min os.window om.window :=
    ((gt_mem_nhds (lt_min os.window_pos om.window_pos)) :
      {ε : ℝ≥0 | ε < min os.window om.window} ∈ 𝓝 0).mono (fun _ he => he.le)
  filter_upwards [hnz, hwindow] with ε hn hε
  have hεs := hε.trans (min_le_left _ _)
  have hidem : os.projection ε (os.projection ε ds.vector) = os.projection ε ds.vector := by
    rw [os.rank_one ε hεs]
    simp only [ContinuousLinearMap.smulRight_apply, map_smul, os.normalization ε hεs, one_smul]
  have hfix : om.projection ε (rightBranch os i ε) = rightBranch os i ε := by
    have he := congrArg (fun B : S →L[ℂ] H => B (os.projection ε ds.vector)) (hagree ε hε)
    simpa only [ContinuousLinearMap.comp_apply, hidem, rightBranch] using he
  change (φ (j (rightBranch os i ε)))⁻¹ *
    φ (j (om.projection ε (rightBranch os i ε))) = 1
  rw [hfix, inv_mul_cancel₀ hn]

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability

namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniPhysicalStability
open KellerLiverani1999 KellerLiveraniMeasureStability

variable {S H W V Z Core X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual positive-noise original-weight probabilities converge weakly.
The source packet uses invariant core actions and true same-cutoff projector
agreement; it contains no regular noisy vector, product integral, convergence
or additional complex spectral-gap hypothesis. -/
theorem tendsto_actual_probability_from_invariant_core
    {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
    {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] V}
    {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
    {qs δs qm δm : ℝ}
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hδsub : δm < qm - dm.subordinate) (hδlead : δm < dm.rate - qm) (hqm : 0 < qm)
    (hi : IsCompactOperator i) (hj : Function.Injective j) (hdense : DenseRange i)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0)
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H)
    (ν : ℝ≥0 → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hconjugation : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), Nonempty (RealOperatorConjugation (Pm ε)))
    (hsources : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), Nonempty
      (InvariantPhysicalPairing.Inputs (Z := Z) (Core := Core)
        (om.projection ε) (((om.eigenvalue ε).re : ℂ)⁻¹ • Pm ε)
        (rightBranch os i ε) (ν ε) A M))
    (hequilibrium : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure X)) =
      realLeftTrace os om φ 0 (M h (i ds.vector))) :
    Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) := by
  let ν' : ℝ≥0 → ProbabilityMeasure X := fun ε => if ε = 0 then ν₀ else ν ε
  have hs : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), 0 < ε → Nonempty
      (InvariantPhysicalPairing.Inputs (Z := Z) (Core := Core)
        (om.projection ε) (((om.eigenvalue ε).re : ℂ)⁻¹ • Pm ε)
        (rightBranch os i ε) (ν ε) A M) := eventually_nhdsWithin_iff.mp hsources
  have hc : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), 0 < ε →
      Nonempty (RealOperatorConjugation (Pm ε)) := eventually_nhdsWithin_iff.mp hconjugation
  have hw : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ om.window :=
    (gt_mem_nhds om.window_pos).mono (fun _ he => he.le)
  have hfull : Tendsto ν' (𝓝 (0 : ℝ≥0)) (𝓝 ν₀) := by
    apply tendsto_probability_of_two_projector_applications os om hi hj hdense hagree
      φ hφ A hA (fun h => (M h).restrictScalars ℝ) ν' ν₀ _ hequilibrium
    intro h
    filter_upwards [hs, hc, hw, eventually_projector_eq_leftTrace os om hagree φ hφ,
      eventually_leftTrace_normalization os om hagree φ hφ]
      with ε hsource hconj hwindow hprojector hnorm
    by_cases hz : ε = 0
    · subst ε
      change (∫ x, h.val x ∂(ν' 0 : Measure X)) =
        realLeftTrace os om φ 0 (M h (rightBranch os i 0))
      have hv : ν' 0 = ν₀ := by simp [ν']
      rw [hv]
      simpa only [rightBranch, os.projection_zero, ContinuousLinearMap.smulRight_apply,
        ds.normalization, one_smul] using hequilibrium h
    · obtain ⟨I⟩ := hsource (pos_iff_ne_zero.mpr hz)
      obtain ⟨conj⟩ := hconj (pos_iff_ne_zero.mpr hz)
      change (∫ x, h.val x ∂(ν' ε : Measure X)) =
        ((leftTrace os om φ ε) (M h (rightBranch os i ε))).re
      have hv : ν' ε = ν ε := by simp [ν', hz]
      rw [hv]
      exact I.integral_eq (leftTrace os om φ ε) hprojector hnorm
        (om.tendsto_normalized_powers hδsub hδlead hqm ε hwindow conj) h
  apply (hfull.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hz : ε ≠ 0 := ne_of_gt hε
  simp [ν', hz]

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniPhysicalStability
