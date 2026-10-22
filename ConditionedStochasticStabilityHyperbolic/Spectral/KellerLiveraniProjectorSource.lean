module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniRankStability
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinementSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicRieszProjector
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorWindowRestriction
public import LeanShared.Analysis.WeakProjectorSeed
public import LeanShared.Analysis.RankOneCommutingEigenvalue
public import LeanShared.Analysis.TwoNormApplicationConvergence
public import LeanShared.Analysis.RieszComplementSpectrum
public import LeanShared.Analysis.RieszContourEigenvectors
import Mathlib.Tactic.Linarith

/-! The full simple-leading Keller--Liverani projector contract follows from
its literal two-norm hypotheses. No noisy spectral data are supplied. -/

public noncomputable section
open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

private theorem projector_source : ClassicalContract (E := E) (W := W) := by
  classical
  intro P i h d q δ hq hqr hqM hsub hδ _ hδgap
  obtain ⟨r, hδr, hrgap⟩ := exists_between hδgap
  obtain ⟨R, hrR, hRgap⟩ := exists_between hrgap
  have hr : 0 < r := hδ.trans hδr
  have gapR : R < d.rate-d.subordinate := by linarith
  have gapr : r < d.rate-d.subordinate := by linarith
  have circleR := d.riesz_circle R (hr.trans hrR) gapR
  have circler := d.riesz_circle r hr gapr
  have lower : ∀ z ∈ closedBall (d.rate : ℂ) R \ ball (d.rate : ℂ) r, q ≤ ‖z‖ := by
    intro z hz
    have hb := norm_sub_norm_le (d.rate : ℂ) z
    have nr : ‖(d.rate : ℂ)‖=d.rate := by simp [abs_of_pos d.rate_pos]
    rw [nr, ←dist_eq_norm, dist_comm] at hb
    have hd : dist z (d.rate : ℂ) ≤ R := hz.1
    linarith
  have annulus : closedBall (d.rate : ℂ) R \ ball (d.rate : ℂ) r ⊆
      resolventSet ℂ (P 0) := by
    intro z hz
    apply circleR.2.1 ⟨hz.1, ?_⟩
    intro he
    apply hz.2
    simpa only [mem_singleton_iff] using he ▸ (mem_ball_self hr :
      (d.rate : ℂ) ∈ ball (d.rate : ℂ) r)
  let proj := fun ε => LeanShared.RieszContourIdempotent.projector (P ε) (d.rate : ℂ) r
  obtain ⟨C, hC, convergence, profile⟩ := h.rank_profile q hq (d.rate : ℂ) r R hr hrR
    circler.1 lower annulus d.mean d.vector d.normalization circler.2.2
  have fixed : (d.mean.smulRight d.vector) d.vector = d.vector := by
    simp only [smulRight_apply, d.normalization, one_smul]
  have coercivity : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ∀ x, ‖proj ε x‖ ≤ C*‖i (proj ε x)‖ := by
    filter_upwards [profile] with ε hh
    exact hh.2.2.2.1
  obtain ⟨vectors, B, hB, bounded⟩ := LeanShared.WeakProjectorSeed.tendsto_and_bound
    proj (d.mean.smulRight d.vector) i d.vector fixed (𝓝 0) C convergence coercivity
  have vnonzero : d.vector ≠ 0 := by
    intro hv
    have hn := d.normalization
    rw [hv, map_zero] at hn
    exact zero_ne_one hn
  have ivnonzero : i d.vector ≠ 0 := by
    intro hi
    exact vnonzero (h.weak_injective (hi.trans (map_zero i).symm))
  obtain ⟨ψ, hψ⟩ := LeanShared.WeakProjectorSeed.normalized_functional (i d.vector) ivnonzero
  have perturb : Tendsto (fun ε => ‖i.comp (P ε-P 0)‖) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      ((NNReal.continuous_coe.tendsto 0).comp h.modulus_zero)
    filter_upwards [eventually_le_nhds h.window_pos] with ε hε
    exact h.perturbation ε hε
  have weakQ : ∀ x, ‖i (P 0 x)‖ ≤ (h.weakConstant*h.weakRate)*‖i x‖ := by
    intro x
    simpa only [pow_one] using h.weak_growth 0 zero_le 1 x
  have applications := LeanShared.TwoNormApplicationConvergence.tendsto P (P 0) i
    (fun ε => proj ε d.vector) d.vector (𝓝 0) B (h.weakConstant*h.weakRate)
    bounded vectors perturb weakQ
  have denominator := ψ.continuous.tendsto (i d.vector) |>.comp vectors
  change Tendsto (fun ε => ψ (i (proj ε d.vector))) (𝓝 0) (𝓝 (ψ (i d.vector))) at denominator
  rw [hψ] at denominator
  have numerator := ψ.continuous.tendsto (i (P 0 d.vector)) |>.comp applications
  change Tendsto (fun ε => ψ (i (P ε (proj ε d.vector)))) (𝓝 0)
    (𝓝 (ψ (i (P 0 d.vector)))) at numerator
  have value : ψ (i (P 0 d.vector)) = (d.rate : ℂ) := by
    rw [d.right_equation, map_smul, map_smul, hψ, smul_eq_mul, mul_one]
  rw [value] at numerator
  let eigenvalue := fun ε => ψ (i (P ε (proj ε d.vector))) / ψ (i (proj ε d.vector))
  have eigenvalue_limit : Tendsto eigenvalue (𝓝 0) (𝓝 (d.rate : ℂ)) := by
    exact (by simpa only [Pi.div_def, div_one] using numerator.div denominator one_ne_zero :
      Tendsto (fun ε => ψ (i (P ε (proj ε d.vector))) / ψ (i (proj ε d.vector)))
        (𝓝 0) (𝓝 (d.rate : ℂ)))
  have denominator_nonzero : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ψ (i (proj ε d.vector)) ≠ 0 :=
    denominator.eventually (isOpen_ne.mem_nhds one_ne_zero)
  have near : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), dist (eigenvalue ε) (d.rate : ℂ) < δ :=
    eigenvalue_limit.eventually (ball_mem_nhds _ hδ)
  let mean : ℝ≥0 → E →L[ℂ] ℂ := fun ε =>
    if hh : ∃ ℓ : E →L[ℂ] ℂ, ℓ (proj ε d.vector)=1 ∧
      proj ε=ℓ.smulRight (proj ε d.vector) then Classical.choose hh else 0
  have means : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), mean ε (proj ε d.vector)=1 ∧
      proj ε=(mean ε).smulRight (proj ε d.vector) := by
    filter_upwards [profile] with ε hh
    have rank : ∃ ℓ : E →L[ℂ] ℂ, ℓ (proj ε d.vector)=1 ∧
        proj ε=ℓ.smulRight (proj ε d.vector) := hh.2.2.2.2
    simpa only [mean, dite_eq_left rank] using Classical.choose_spec rank
  obtain ⟨conf⟩ := classicalConfinementContract P i h q δ hq hqM hδ
  have good := profile.and (means.and (denominator_nonzero.and
    (near.and (eventually_le_nhds conf.window_pos))))
  obtain ⟨η, hη, goodη⟩ := exists_positive_window_of_eventually good
  refine ⟨{
    window := η
    window_pos := hη
    eigenvalue := eigenvalue
    projection := proj
    vector := fun ε => proj ε d.vector
    mean := mean
    eigenvalue_near := fun ε hε => (goodη ε hε).2.2.2.1
    rank_one := fun ε hε => (goodη ε hε).2.1.2
    normalization := fun ε hε => (goodη ε hε).2.1.1
    eigen_action := ?_
    projection_commutes := fun ε hε => (goodη ε hε).1.2.2.1
    project_eigenvector := ?_
    spectral_confinement := ?_
    remainder_spectrum := ?_
    projection_zero := circler.2.2
    eigenvalue_convergence := eigenvalue_limit
    projector_convergence := ?_
    coercivityConstant := C
    coercivityConstant_nonneg := hC
    range_coercivity := fun ε hε => (goodη ε hε).1.2.2.2.1 }⟩
  · intro ε hε
    have hg := goodη ε hε
    exact (LeanShared.RankOneCommutingEigenvalue.eigen_action (P ε) (proj ε)
      (mean ε) (ψ.comp i) (proj ε d.vector) hg.2.1.2 hg.2.1.1 hg.1.2.2.1
      hg.2.2.1).2
  · intro ε hε z hz x hx
    exact LeanShared.RieszContourIdempotent.projector_eigenvector (P ε)
      (d.rate : ℂ) z r hr (goodη ε hε).1.1 (hz.trans_lt hδr) x hx
  · intro ε hε z hz
    exact conf.spectrum_near ε (goodη ε hε).2.2.2.2 z hz
  · intro ε hε z hz
    have hg := goodη ε hε
    have action := (LeanShared.RankOneCommutingEigenvalue.eigen_action (P ε) (proj ε)
      (mean ε) (ψ.comp i) (proj ε d.vector) hg.2.1.2 hg.2.1.1 hg.1.2.2.1
      hg.2.2.1).2
    have inclusion := LeanShared.RieszComplementSpectrum.inclusion (P ε) (d.rate : ℂ)
      (eigenvalue ε) r hr.le hg.1.1 (hg.2.2.2.1.trans hδr) hg.1.2.1
      action (hg.1.2.2.1.symm.trans action) z hz
    exact inclusion.imp id (fun hh => ⟨hh.1,hδr.trans_le hh.2⟩)
  · have zero : proj 0 = d.mean.smulRight d.vector := circler.2.2
    rw [zero]
    exact convergence

/-- Full KL1999 simple-leading projector stability is a proved theorem. -/
theorem classicalContract : ClassicalContract (E := E) (W := W) := projector_source

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
