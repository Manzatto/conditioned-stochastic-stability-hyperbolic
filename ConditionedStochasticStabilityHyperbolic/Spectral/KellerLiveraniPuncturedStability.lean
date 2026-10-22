module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniPhysicalStability

/-! # Physical stochastic stability uses positive noise scales only

The deterministic zero-noise operator need not be strong Feller or possess a
volume density. Physical smoothing and product source facts are used only for
positive noise. An auxiliary probability at zero is the deterministic
equilibrium measure; its integral identification is the cited deterministic
spectral fact. The resulting actual limit is along the positive-noise filter.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
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

theorem tendsto_actual_probability_from_positive_noise_sources
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
    (hsources : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), Nonempty
      (PhysicalInputs (Z := Z) (Reg := Reg) (Core := Core)
        (om.projection ε) (rightBranch os i ε) (ν ε) A M))
    (hequilibrium : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure X)) =
      realLeftTrace os om φ 0 (M h (i ds.vector))) :
    Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) := by
  let ν' : ℝ≥0 → ProbabilityMeasure X := fun ε => if ε = 0 then ν₀ else ν ε
  have hs : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), 0 < ε → Nonempty
      (PhysicalInputs (Z := Z) (Reg := Reg) (Core := Core)
        (om.projection ε) (rightBranch os i ε) (ν ε) A M) :=
    eventually_nhdsWithin_iff.mp hsources
  have hfull : Tendsto ν' (𝓝 (0 : ℝ≥0)) (𝓝 ν₀) := by
    apply tendsto_probability_of_two_projector_applications os om hi hj hdense hagree
      φ hφ A hA (fun h => (M h).restrictScalars ℝ) ν' ν₀ _ hequilibrium
    intro h
    filter_upwards [hs, eventually_projector_eq_leftTrace os om hagree φ hφ]
      with ε hsource hprojector
    by_cases hz : ε = 0
    · subst ε
      change (∫ x, h.val x ∂(ν' 0 : Measure X)) =
        realLeftTrace os om φ 0 (M h (rightBranch os i 0))
      have hv : ν' 0 = ν₀ := by simp [ν']
      rw [hv]
      simpa only [rightBranch, os.projection_zero, ContinuousLinearMap.smulRight_apply,
        ds.normalization, one_smul] using hequilibrium h
    · obtain ⟨I⟩ := hsource (pos_iff_ne_zero.mpr hz)
      change (∫ x, h.val x ∂(ν' ε : Measure X)) =
        ((leftTrace os om φ ε) (M h (rightBranch os i ε))).re
      have hv : ν' ε = ν ε := by simp [ν', hz]
      rw [hv]
      exact I.integral_eq (leftTrace os om φ ε) hprojector h

  apply (hfull.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hz : ε ≠ 0 := ne_of_gt hε
  simp [ν', hz]

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniPhysicalStability
