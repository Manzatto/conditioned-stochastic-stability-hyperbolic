module

public import LeanShared.Analysis.SpectralProductConvergence
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Recovering left eigenfunctionals from rank-one projections

A fixed separating functional recovers the scalar coefficient of a rank-one
projection. Consequently weak projection convergence implies convergence of
left eigenfunctionals; a uniform projection bound and a lower bound on the
right vectors imply a uniform dual bound. These are the deductions needed
between spectral perturbation and product-measure stability.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanShared.RankOneProjectorConvergence

variable {E W ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {L : Filter ι}

/-- Weak convergence of right vectors and of their rank-one products determines
convergence of the scalar coefficient, without a priori dual convergence. -/
theorem tendsto_coefficient
    (g : ι → W) (g₀ : W) (hg₀ : g₀ ≠ 0)
    (a : ι → ℝ) (a₀ : ℝ)
    (hg : Tendsto g L (𝓝 g₀))
    (hprod : Tendsto (fun n => a n • g n) L (𝓝 (a₀ • g₀))) :
    Tendsto a L (𝓝 a₀) := by
  obtain ⟨φ, _, hφ⟩ := exists_dual_vector ℝ g₀ (norm_ne_zero_iff.mpr hg₀)
  have hden := φ.continuous.continuousAt.tendsto.comp hg
  have hnum := φ.continuous.continuousAt.tendsto.comp hprod
  have hnz : φ g₀ ≠ 0 := by rw [hφ]; exact norm_ne_zero_iff.mpr hg₀
  have he : ∀ᶠ n in L, φ (g n) ≠ 0 := hden.eventually_ne hnz
  have hlim := hnum.div hden hnz
  have hr : φ (a₀ • g₀) / φ g₀ = a₀ := by
    rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hnz]
  rw [hr] at hlim
  apply hlim.congr'
  filter_upwards [he] with n hn
  change φ (a n • g n) / φ (g n) = a n
  rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hn]

/-- Apply the scalar recovery to each test of the spectral projector. -/
theorem tendsto_dual_of_projectors
    (j : E →L[ℝ] W) (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (g : ι → E) (g₀ : E) (hg₀ : j g₀ ≠ 0)
    (hg : Tendsto (fun n => j (g n)) L (𝓝 (j g₀)))
    (D : Set E)
    (hproj : ∀ x ∈ D, Tendsto (fun n => j ((μ n x) • g n))
      L (𝓝 (j ((μ₀ x) • g₀)))) :
    ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)) := by
  intro x hx
  apply tendsto_coefficient (fun n => j (g n)) (j g₀) hg₀ _ _ hg
  simpa only [map_smul] using hproj x hx

/-- A bounded rank-one projector gives a dual bound once the right vector is
bounded away from zero. -/
theorem norm_dual_le_of_projector
    (μ : E →L[ℝ] ℝ) (g : E) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (hg : c ≤ ‖g‖) (hproj : ‖μ.smulRight g‖ ≤ K) : ‖μ‖ ≤ K / c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hK hc.le)
  intro x
  have h := (μ.smulRight g).le_opNorm x
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs] at h
  have hb : |μ x| * c ≤ K * ‖x‖ :=
    (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans
      (h.trans (mul_le_mul_of_nonneg_right hproj (norm_nonneg _)))
  rw [Real.norm_eq_abs]
  have he : K / c * ‖x‖ = (K * ‖x‖) / c := by ring
  rw [he]
  exact (le_div_iff₀ hc).mpr hb

/-- Convergence to a nonzero right vector turns an eventual uniform projector
bound into an eventual uniform dual bound, with an explicit constant. -/
theorem eventually_norm_dual_le
    (μ : ι → E →L[ℝ] ℝ) (g : ι → E) (g₀ : E) (hg₀ : g₀ ≠ 0)
    (hg : Tendsto g L (𝓝 g₀)) (K : ℝ) (hK : 0 ≤ K)
    (hproj : ∀ᶠ n in L, ‖(μ n).smulRight (g n)‖ ≤ K) :
    ∀ᶠ n in L, ‖μ n‖ ≤ K / (‖g₀‖ / 2) := by
  have hc : 0 < ‖g₀‖ / 2 := div_pos (norm_pos_iff.mpr hg₀) (by norm_num)
  have hless : ‖g₀‖ / 2 < ‖g₀‖ := by nlinarith [norm_pos_iff.mpr hg₀]
  have hlow := hg.norm.eventually (lt_mem_nhds hless)
  filter_upwards [hproj, hlow] with n hn hgn
  exact norm_dual_le_of_projector (μ n) (g n) K (‖g₀‖ / 2) hK hc hgn.le hn

/-- Keller--Liverani's range coercivity converts weak convergence of the
projected right vectors into a uniform strong bound. -/
theorem eventually_norm_right_le
    (j : E →L[ℝ] W) (g : ι → E) (g₀ : W)
    (hg : Tendsto (fun n => j (g n)) L (𝓝 g₀))
    (K : ℝ) (hK : 0 ≤ K)
    (hcoercive : ∀ᶠ n in L, ‖g n‖ ≤ K * ‖j (g n)‖) :
    ∀ᶠ n in L, ‖g n‖ ≤ K * (‖g₀‖ + 1) := by
  have hupper := hg.norm.eventually (gt_mem_nhds (show ‖g₀‖ < ‖g₀‖ + 1 by linarith))
  filter_upwards [hcoercive, hupper] with n hn hu
  exact hn.trans (mul_le_mul_of_nonneg_left hu.le hK)

end LeanShared.RankOneProjectorConvergence
