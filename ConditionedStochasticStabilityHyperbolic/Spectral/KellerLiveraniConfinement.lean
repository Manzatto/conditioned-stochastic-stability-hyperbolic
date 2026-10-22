module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
import Mathlib.Tactic.Linarith

/-! # KL spectral confinement without a simple leading eigenvalue

Theorem 1 of Keller--Liverani 1999 controls the whole spectrum outside a
contraction disk. This separate classical contract requires neither mixing,
rank one nor a peripheral exclusion assumption. Its consequence is an
explicit eventual raw spectral-radius bound for subordinate layers.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology NNReal ENNReal

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

structure ConfinementOutputs (P : ℝ≥0 → E →L[ℂ] E) (q δ : ℝ) where
  window : ℝ≥0
  window_pos : 0 < window
  spectrum_near : ∀ ε ≤ window, ∀ z ∈ spectrum ℂ (P ε),
    ‖z‖ ≤ q ∨ ∃ w ∈ spectrum ℂ (P 0), dist z w ≤ δ

/-- Primary KL1999 Theorem 1 confinement, independent of Corollary 1 rank
stability. No leading spectral data are an argument. -/
def ClassicalConfinementContract [CompleteSpace E] : Prop :=
  ∀ (P : ℝ≥0 → E →L[ℂ] E) (i : E →L[ℂ] W) (h : Hypotheses P i) (q δ : ℝ),
    h.alpha < q → q < h.weakRate → 0 < δ → Nonempty (ConfinementOutputs P q δ)

/-- Convert a real upper spectral-radius bound to a pointwise spectral bound. -/
theorem norm_mem_spectrum_le_of_radius_le
    (Q : E →L[ℂ] E) (r : ℝ) (hr : 0 ≤ r)
    (hQ : spectralRadius ℂ Q ≤ ENNReal.ofReal r)
    {z : ℂ} (hz : z ∈ spectrum ℂ Q) : ‖z‖ ≤ r := by
  have hb : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ Q := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  have hle : ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm] using hb.trans hQ
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp hle

/-- Confinement keeps every raw spectrum uniformly below a chosen slack
rate. Multiple periodic/peripheral deterministic eigenvalues are allowed. -/
theorem ConfinementOutputs.eventually_raw_radius_lt [CompleteSpace E] [Nontrivial E]
    {P : ℝ≥0 → E →L[ℂ] E} {q δ : ℝ}
    (o : ConfinementOutputs P q δ) (s scale R : ℝ)
    (hscale : 0 < scale) (hR : 0 < R)
    (hdet : ∀ z ∈ spectrum ℂ (P 0), ‖z‖ ≤ s)
    (hq : scale * q < R) (hsδ : scale * (s + δ) < R) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), spectralRadius ℂ ((scale : ℂ) • P ε) < ENNReal.ofReal R := by
  have hε : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ o.window :=
    ((gt_mem_nhds o.window_pos) : {ε : ℝ≥0 | ε < o.window} ∈ 𝓝 0).mono (fun _ he => he.le)
  filter_upwards [hε] with ε he
  rw [ENNReal.ofReal_eq_coe_nnreal hR.le]
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  rw [spectrum.smul_eq_smul (scale : ℂ) (P ε) (spectrum.nonempty (P ε))] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  change ‖(scale : ℂ) • v‖ < R
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hscale.le]
  obtain hsmall | ⟨w, hw, hvw⟩ := o.spectrum_near ε he v hv
  · exact (mul_le_mul_of_nonneg_left hsmall hscale.le).trans_lt hq
  · have ht : ‖v‖ ≤ dist v w + ‖w‖ := by
      simpa only [sub_add_cancel, dist_eq_norm] using norm_add_le (v - w) w
    have hbound : ‖v‖ ≤ s + δ := by linarith [hdet w hw]
    exact (mul_le_mul_of_nonneg_left hbound hscale.le).trans_lt hsδ

/-- An arbitrary deterministic raw-radius upper bound below the target
produces an eventual noisy raw-radius bound from primary KL confinement.
The normalized essential/contraction rate must also lie below that target. -/
theorem eventually_subordinate_raw_radius_lt [CompleteSpace E] [Nontrivial E]
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
    (hKL : ClassicalConfinementContract (E := E) (W := W)) (h : Hypotheses P i)
    (scale s R : ℝ) (hscale : 0 < scale) (hs : 0 ≤ s)
    (hdet : spectralRadius ℂ ((scale : ℂ) • P 0) ≤ ENNReal.ofReal s)
    (hsR : s < R) (hαR : scale * h.alpha < R) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), spectralRadius ℂ ((scale : ℂ) • P ε) < ENNReal.ofReal R := by
  have hR : 0 < R := hs.trans_lt hsR
  have hαt : h.alpha < R / scale := (lt_div_iff₀ hscale).mpr (by simpa only [mul_comm] using hαR)
  let top := min h.weakRate (R / scale)
  have hat : h.alpha < top := lt_min h.alpha_lt_weakRate hαt
  let q := (h.alpha + top) / 2
  have hαq : h.alpha < q := by dsimp only [q]; linarith
  have hqt : q < top := by dsimp only [q]; linarith
  have hqM : q < h.weakRate := hqt.trans_le (min_le_left _ _)
  have hqR : scale * q < R := by
    have := hqt.trans_le (min_le_right _ _)
    simpa only [mul_comm] using (lt_div_iff₀ hscale).mp this
  let δ := (R / scale - s / scale) / 2
  have hst : s / scale < R / scale := (div_lt_div_iff_of_pos_right hscale).mpr hsR
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hsum : scale * (s / scale + δ) < R := by
    have ht : s / scale + δ < R / scale := by dsimp only [δ]; linarith
    simpa only [mul_comm] using (lt_div_iff₀ hscale).mp ht
  obtain ⟨o⟩ := hKL P i h q δ hαq hqM hδ
  apply o.eventually_raw_radius_lt (s / scale) scale R hscale hR _ hqR hsum
  intro z hz
  have hsz : (scale : ℂ) • z ∈ spectrum ℂ ((scale : ℂ) • P 0) := by
    rw [spectrum.smul_eq_smul (scale : ℂ) (P 0) (spectrum.nonempty (P 0))]
    exact ⟨z, hz, rfl⟩
  have hb := norm_mem_spectrum_le_of_radius_le _ s hs hdet hsz
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hscale.le] at hb
  apply (le_div_iff₀ hscale).mpr
  simpa only [mul_comm] using hb

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
