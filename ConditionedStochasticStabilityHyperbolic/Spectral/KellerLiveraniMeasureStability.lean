module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorStability
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Linarith

/-! # Actual probability stability from the two KL projector applications

The strong-space right branch is `Pi_e gamma_0`. Strong boundedness and weak
convergence follow from that KL application. Compact inclusion upgrades the
right branch to the intermediate norm. A fixed weak separator normalizes the
intermediate projector into its left functional; the second KL application
gives its uniform norm bound. Strong/intermediate projector agreement gives
dense-core dual convergence. No strong vector bound or dual convergence is an
input. Physical measure-product representations may be established on the
retained region only; no global identification of the cutoff eigenfunction
with the original-weight eigenfunction is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability

open KellerLiverani1999

variable {S H W V X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
  {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] V}
  {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
  {qs δs qm δm : ℝ}

/-- The actual right branch in the compact intermediate space. -/
def rightBranch (os : ProjectorOutputs Ps (j.comp i) ds qs δs) (i : S →L[ℂ] H)
    (ε : ℝ≥0) : H := i (os.projection ε ds.vector)

/-- Normalize the intermediate projector using one fixed weak separator.
Inverse zero defines an arbitrary harmless extension outside the eventual
nonzero-denominator neighborhood. -/
def leftTrace (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm) (φ : W →L[ℂ] ℂ) (ε : ℝ≥0) : H →L[ℂ] ℂ :=
  (φ (j (rightBranch os i ε)))⁻¹ • ((φ.comp j).comp (om.projection ε))

/-- Real integration functionals recovered from complex spectral pairings. -/
def realLeftTrace (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm) (φ : W →L[ℂ] ℂ) (ε : ℝ≥0) : H →L[ℝ] ℝ :=
  Complex.reCLM.comp ((leftTrace os om φ ε).restrictScalars ℝ)

/-- The two checked KL projector outputs imply weak convergence of actual
probabilities represented by their normalized spectral products. -/
theorem tendsto_probability_of_two_projector_applications
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hi : IsCompactOperator i) (hj : Function.Injective j) (hdense : DenseRange i)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0)
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℝ] H)
    (ν : ℝ≥0 → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hrepresentation : ∀ h : A, ∀ᶠ ε in 𝓝 (0 : ℝ≥0),
      (∫ x, h.val x ∂(ν ε : Measure X)) =
        realLeftTrace os om φ ε (M h (rightBranch os i ε)))
    (hequilibrium : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure X)) =
      realLeftTrace os om φ 0 (M h (i ds.vector))) :
    Tendsto ν (𝓝 (0 : ℝ≥0)) (𝓝 ν₀) := by
  let γs := fun ε => os.projection ε ds.vector
  let γ := rightBranch os i
  have hweak : Tendsto (fun ε => j (i (γs ε))) (𝓝 (0 : ℝ≥0)) (𝓝 (j (i ds.vector))) :=
    os.projected_vector_weak_convergence
  let Ks := os.coercivityConstant * (‖(j.comp i).comp (os.projection 0)‖ + 1)
  have hγs : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ‖γs ε‖ ≤ Ks * ‖ds.vector‖ := by
    filter_upwards [os.eventually_norm_projection_le] with ε he
    exact ((os.projection ε).le_opNorm ds.vector).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hγ : Tendsto γ (𝓝 (0 : ℝ≥0)) (𝓝 (i ds.vector)) :=
    LeanShared.SpectralProductConvergence.tendsto_intermediate_of_compact
      (i.restrictScalars ℝ) hi (j.restrictScalars ℝ) hj γs _ hγs (i ds.vector) hweak
  have hden : Tendsto (fun ε => φ (j (γ ε))) (𝓝 (0 : ℝ≥0)) (𝓝 (φ (j (i ds.vector)))) :=
    φ.continuous.continuousAt.tendsto.comp hweak
  let a₀ := φ (j (i ds.vector))
  let c := ‖a₀‖ / 2
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hφ) (by norm_num)
  have hlow : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), c ≤ ‖φ (j (γ ε))‖ := by
    have hless : c < ‖a₀‖ := by dsimp only [c]; linarith [norm_pos_iff.mpr hφ]
    exact (hden.norm.eventually (lt_mem_nhds hless)).mono (fun _ he => he.le)
  let Km := om.coercivityConstant * (‖jm.comp (om.projection 0)‖ + 1)
  have hKm : 0 ≤ Km := mul_nonneg om.coercivityConstant_nonneg (by positivity)
  let B := ‖φ.comp j‖ * Km / c
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (norm_nonneg _) hKm) hc.le
  have hdual : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ‖realLeftTrace os om φ ε‖ ≤ B := by
    filter_upwards [hlow, om.eventually_norm_projection_le] with ε ha hp
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro x
    have hleftnorm : ‖leftTrace os om φ ε x‖ ≤ B * ‖x‖ := by
      change ‖(φ (j (γ ε)))⁻¹ • ((φ.comp j).comp (om.projection ε)) x‖ ≤ _
      rw [norm_smul, norm_inv]
      have hpv : ‖om.projection ε x‖ ≤ Km * ‖x‖ :=
        ((om.projection ε).le_opNorm x).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      have hnum : ‖((φ.comp j).comp (om.projection ε)) x‖ ≤ ‖φ.comp j‖ * (Km * ‖x‖) :=
        ((φ.comp j).le_opNorm _).trans (mul_le_mul_of_nonneg_left hpv (norm_nonneg _))
      have hinv : ‖φ (j (γ ε))‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc ha
      calc
        _ ≤ c⁻¹ * (‖φ.comp j‖ * (Km * ‖x‖)) :=
          mul_le_mul hinv hnum (norm_nonneg _) (inv_nonneg.mpr hc.le)
        _ = B * ‖x‖ := by dsimp only [B]; ring
    exact (Complex.abs_re_le_norm _).trans hleftnorm
  have hwindow : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ min os.window om.window :=
    ((gt_mem_nhds (lt_min os.window_pos om.window_pos)) :
      {ε : ℝ≥0 | ε < min os.window om.window} ∈ 𝓝 0).mono (fun _ he => he.le)
  have hcore : ∀ x ∈ Set.range i, Tendsto (fun ε => realLeftTrace os om φ ε x)
      (𝓝 (0 : ℝ≥0)) (𝓝 (realLeftTrace os om φ 0 x)) := by
    rintro x ⟨y, rfl⟩
    have hproj := (ContinuousLinearMap.apply ℂ W y).continuous.continuousAt.tendsto.comp
      os.projector_convergence
    have hzero : os.projection 0 ds.vector = ds.vector := by
      rw [os.projection_zero, ContinuousLinearMap.smulRight_apply, ds.normalization, one_smul]
    have hnumS : Tendsto (fun ε => φ (j (i (os.projection ε y)))) (𝓝 (0 : ℝ≥0))
        (𝓝 (φ (j (i (os.projection 0 y))))) := by
      have hl := hproj.add_const (j (i (os.projection 0 y)))
      have hln : Tendsto (fun ε => j (i (os.projection ε y))) (𝓝 (0 : ℝ≥0))
          (𝓝 (j (i (os.projection 0 y)))) := by
        simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
          sub_apply, map_sub, sub_add_cancel, zero_apply, zero_add] using hl
      exact φ.continuous.continuousAt.tendsto.comp hln
    have hnum : Tendsto (fun ε => φ (j (om.projection ε (i y)))) (𝓝 (0 : ℝ≥0))
        (𝓝 (φ (j (om.projection 0 (i y))))) := by
      have hz := congrArg (fun T : S →L[ℂ] H => T y) (hagree 0 (by positivity))
      simp only [ContinuousLinearMap.comp_apply] at hz
      rw [hz]
      apply hnumS.congr'
      filter_upwards [hwindow] with ε he
      have heq := congrArg (fun T : S →L[ℂ] H => T y) (hagree ε he)
      simp only [ContinuousLinearMap.comp_apply] at heq
      exact congrArg (fun v : H => φ (j v)) heq.symm
    have hden0 : φ (j (γ 0)) = a₀ := by
      change φ (j (i (os.projection 0 ds.vector))) = a₀
      rw [hzero]
    have hquot := hnum.div hden hφ
    have hreal := Complex.continuous_re.continuousAt.tendsto.comp hquot
    change Tendsto (fun ε => ((φ (j (γ ε)))⁻¹ * φ (j (om.projection ε (i y)))).re)
      (𝓝 (0 : ℝ≥0))
      (𝓝 (((φ (j (γ 0)))⁻¹ * φ (j (om.projection 0 (i y)))).re))
    simpa only [Function.comp_def, Pi.div_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv, mul_comm, hden0, a₀] using hreal

  have hμ : ∀ x, Tendsto (fun ε => realLeftTrace os om φ ε x)
      (𝓝 (0 : ℝ≥0)) (𝓝 (realLeftTrace os om φ 0 x)) :=
    LeanShared.SpectralProductConvergence.tendsto_apply_of_dense _ _ B hB hdual
      (Set.range i) hdense hcore
  apply QuasiErgodicStability.tendsto_probabilityMeasure_of_dense_tests ν ν₀ A hA
  intro h hh
  let test : A := ⟨h, hh⟩
  have hlim := LeanShared.SpectralProductConvergence.tendsto_apply_moving
    (fun ε => realLeftTrace os om φ ε) (realLeftTrace os om φ 0) B hB hdual hμ
    (fun ε => M test (γ ε)) (M test (i ds.vector))
    ((M test).continuous.continuousAt.tendsto.comp hγ)
  rw [← hequilibrium test] at hlim
  apply hlim.congr'
  filter_upwards [hrepresentation test] with ε he
  exact he.symm

/-- A weak separator always exists for the normalized deterministic vector
when the two actual embeddings are injective. -/
theorem exists_weak_separator (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ φ : W →L[ℂ] ℂ, ‖φ‖ = 1 ∧ φ (j (i ds.vector)) ≠ 0 := by
  have hg : ds.vector ≠ 0 := by
    intro hz
    have h := ds.normalization
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hweak : j (i ds.vector) ≠ 0 := by
    intro hz
    apply hg
    apply hi
    apply hj
    simpa only [map_zero] using hz
  obtain ⟨φ, hnorm, hvalue⟩ := exists_dual_vector ℂ (j (i ds.vector)) (norm_ne_zero_iff.mpr hweak)
  refine ⟨φ, hnorm, ?_⟩
  rw [hvalue]
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hweak)

/-- The normalized weak trace is the actual left coefficient of the
intermediate Riesz projector. Thus the probability representation can use
this constructed functional instead of an independently supplied dual. -/
theorem eventually_projector_eq_leftTrace
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), om.projection ε =
      (leftTrace os om φ ε).smulRight (rightBranch os i ε) := by
  have hden := φ.continuous.continuousAt.tendsto.comp os.projected_vector_weak_convergence
  have hnz : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), φ (j (rightBranch os i ε)) ≠ 0 := hden.eventually_ne hφ
  have hwindow : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ min os.window om.window :=
    ((gt_mem_nhds (lt_min os.window_pos om.window_pos)) :
      {ε : ℝ≥0 | ε < min os.window om.window} ∈ 𝓝 0).mono (fun _ he => he.le)
  filter_upwards [hnz, hwindow] with ε hnonzero hε
  have hεs : ε ≤ os.window := hε.trans (min_le_left _ _)
  have hεm : ε ≤ om.window := hε.trans (min_le_right _ _)
  let γ := rightBranch os i ε
  have hfixS : os.projection ε (os.projection ε ds.vector) = os.projection ε ds.vector := by
    rw [os.rank_one ε hεs]
    simp only [ContinuousLinearMap.smulRight_apply, map_smul, os.normalization ε hεs,
      one_smul]
  have hfix : om.projection ε γ = γ := by
    have he := congrArg (fun T : S →L[ℂ] H => T (os.projection ε ds.vector)) (hagree ε hε)
    simpa only [ContinuousLinearMap.comp_apply, hfixS, γ, rightBranch] using he
  let a := om.mean ε γ
  let b := φ (j (om.vector ε))
  have hγ : γ = a • om.vector ε := by
    rw [← hfix, om.rank_one ε hεm, ContinuousLinearMap.smulRight_apply]
  have hab : a * b ≠ 0 := by
    have hdeneq : φ (j γ) = a * b := by rw [hγ, map_smul, map_smul, smul_eq_mul]
    rwa [hdeneq] at hnonzero
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp hab).1
  have hb : b ≠ 0 := (mul_ne_zero_iff.mp hab).2
  ext x
  rw [om.rank_one ε hεm, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply]
  change om.mean ε x • om.vector ε =
    ((φ (j γ))⁻¹ * φ (j (om.projection ε x))) • γ
  have hdeneq : φ (j γ) = a * b := by rw [hγ, map_smul, map_smul, smul_eq_mul]
  have hnumeq : φ (j (om.projection ε x)) = om.mean ε x * b := by
    rw [om.rank_one ε hεm, ContinuousLinearMap.smulRight_apply, map_smul, map_smul, smul_eq_mul]
  rw [hdeneq, hnumeq, hγ, smul_smul]
  congr 1
  field_simp

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
