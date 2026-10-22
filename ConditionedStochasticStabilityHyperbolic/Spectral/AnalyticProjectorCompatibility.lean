module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniRieszGap

/-! Actual completed transfer compatibility determines the two KL leading
projectors. Their power limits give projector compatibility, so no new
family-specific Riesz comparison is needed between these two analytic spaces. -/

@[expose] public noncomputable section
open Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E F U V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [CompleteSpace E] [CompleteSpace F] in
theorem comp_projectors_of_normalized_power_limits
    (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (i : E →L[ℂ] F) (z : ℂ)
    (Pa : E →L[ℂ] E) (Pb : F →L[ℂ] F)
    (hPQ : i.comp P = Q.comp i)
    (hP : Tendsto (fun n : ℕ => (z⁻¹ • P)^n) atTop (𝓝 Pa))
    (hQ : Tendsto (fun n : ℕ => (z⁻¹ • Q)^n) atTop (𝓝 Pb)) :
    Pb.comp i = i.comp Pa := by
  have hcomm (x : E) : i ((z⁻¹ • P) x) = (z⁻¹ • Q) (i x) := by
    have hh := congrArg (fun T : E →L[ℂ] F => T x) hPQ
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using congrArg (z⁻¹ • ·) hh
  have hpowers (n : ℕ) (x : E) : i (((z⁻¹ • P)^n) x) = ((z⁻¹ • Q)^n) (i x) := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [pow_succ', mul_apply_eq_comp, hcomm, ih]
  ext x
  have hl := i.continuous.continuousAt.tendsto.comp
    ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt.tendsto.comp hP)
  have hr := (ContinuousLinearMap.apply ℂ F (i x)).continuous.continuousAt.tendsto.comp hQ
  exact tendsto_nhds_unique hr (hl.congr' (Eventually.of_forall fun n => hpowers n x))

theorem eventually_projector_comparison_of_intertwining
    {P : ℝ≥0 → E →L[ℂ] E} {Q : ℝ≥0 → F →L[ℂ] F}
    {a : E →L[ℂ] U} {b : F →L[ℂ] V}
    {d : DeterministicLeading (P 0)} {e : DeterministicLeading (Q 0)} {q δ r η : ℝ}
    (os : ProjectorOutputs P a d q δ) (om : ProjectorOutputs Q b e r η)
    (hδsub : δ < q - d.subordinate) (hδlead : δ < d.rate - q) (hq : 0 < q)
    (hηsub : η < r - e.subordinate) (hηlead : η < e.rate - r) (hr : 0 < r)
    (i : E →L[ℂ] F) (hi : Function.Injective i) (hstrong : r < d.rate)
    (hcomm : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), i.comp (P ε) = (Q ε).comp i)
    (hconjS : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), Nonempty (RealOperatorConjugation (P ε)))
    (hconjM : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), Nonempty (RealOperatorConjugation (Q ε))) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), (om.projection ε).comp i = i.comp (os.projection ε) := by
  have hnorm : Tendsto (fun ε => ‖os.eigenvalue ε‖) (𝓝 0) (𝓝 d.rate) := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg d.rate_pos.le] using os.eigenvalue_convergence.norm
  have habove : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), r < ‖os.eigenvalue ε‖ := hnorm.eventually (lt_mem_nhds hstrong)
  have hwin : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ min os.window om.window :=
    (gt_mem_nhds (lt_min os.window_pos om.window_pos)).mono (fun _ h => h.le)
  filter_upwards [hcomm, hconjS, hconjM, habove, hwin] with ε hPQ hcs hcm ha hε
  obtain ⟨cs⟩ := hcs
  obtain ⟨cm⟩ := hcm
  have hεs := hε.trans (min_le_left _ _)
  have hεm := hε.trans (min_le_right _ _)
  have hv : os.vector ε ≠ 0 := by
    intro hz
    have hh := os.normalization ε hεs
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  have hiv : i (os.vector ε) ≠ 0 := fun hz => hv (hi (by simpa only [map_zero] using hz))
  have heigen : Q ε (i (os.vector ε)) = os.eigenvalue ε • i (os.vector ε) := by
    have hh := congrArg (fun T : E →L[ℂ] F => T (os.vector ε)) hPQ
    simpa only [ContinuousLinearMap.comp_apply, os.right_equation ε hεs, map_smul] using hh.symm
  have hvalue := om.eigenvalue_eq_of_above_cutoff hηsub ε hεm _ hiv _ heigen ha
  have hre : (os.eigenvalue ε).re = (om.eigenvalue ε).re := congrArg Complex.re hvalue
  apply comp_projectors_of_normalized_power_limits (P ε) (Q ε) i
    ((os.eigenvalue ε).re : ℂ) (os.projection ε) (om.projection ε) hPQ
    (os.tendsto_normalized_powers hδsub hδlead hq ε hεs cs)
  rw [hre]
  exact om.tendsto_normalized_powers hηsub hηlead hr ε hεm cm

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
