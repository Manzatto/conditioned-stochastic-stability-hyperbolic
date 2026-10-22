module

public import LeanShared.Analysis.CompactTwoNormDecomposition
public import LeanShared.Analysis.StableRangeSpectralIsolation
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith

/-! Discreteness and finiteness of the outer spectrum from actual two-norm
estimates. Spectral isolation is derived rather than assumed. -/

public section
open ContinuousLinearMap Submodule Set
namespace LeanShared.CompactTwoNormDiscreteSpectrum
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Every point outside the strong growth disk has a punctured resolvent
neighbourhood, obtained from the actual finite-dimensional Fitting splitting. -/
theorem punctured_resolvent (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r \ {z} ⊆ resolventSet ℂ T := by
  obtain ⟨n, _, compl, kernels, ranges⟩ :=
    CompactTwoNormDecomposition.exists_decomposition T i hi α R C D hα hR hC hD estimate z hz
  obtain ⟨r, hr, hlocal⟩ := StableRangeSpectralIsolation.exists_punctured_injective
    (T - z • 1) n compl (kernels 1) (ranges 1)
  refine ⟨min r (‖z‖ - α), lt_min hr (sub_pos.mpr hz), ?_⟩
  intro w hw
  have hdist : ‖w - z‖ < min r (‖z‖ - α) := by simpa only [Metric.mem_ball, dist_eq_norm] using hw.1
  have hdiff : w - z ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_singleton_iff] using hw.2)
  have hinjLocal := hlocal (w - z) (hdist.trans_le (min_le_left _ _)) hdiff
  have heq : (T - z • 1) - (w - z) • (1 : E →L[ℂ] E) = T - w • 1 := by
    rw [sub_smul]
    abel
  rw [heq] at hinjLocal
  have hnorm : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
    have hh := norm_add_le w (z - w)
    simpa only [add_sub_cancel, norm_sub_rev] using hh
  have hwα : α < ‖w‖ := by linarith [hdist.trans_le (min_le_right r (‖z‖ - α))]
  have hsurj := CompactTwoNormFredholm.surjective_of_twoNorm T i hi α R C D
    hα hR hC hD estimate w hwα hinjLocal
  have hunit : IsUnit (T - w • 1) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinjLocal, hsurj⟩
  change IsUnit (w • (1 : E →L[ℂ] E) - T)
  simpa only [neg_sub] using hunit.neg

/-- There are only finitely many spectral values outside every strictly
larger closed disk than the strong growth disk. -/
theorem finite_outer_spectrum (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (q : ℝ) (hq : α < q) :
    {z ∈ spectrum ℂ T | q ≤ ‖z‖}.Finite := by
  let K := {z ∈ spectrum ℂ T | q ≤ ‖z‖}
  have compact : IsCompact K := (spectrum.isCompact T).inter_right
    (isClosed_le continuous_const continuous_norm)
  have discrete : IsDiscrete K := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    obtain ⟨r, hr, hball⟩ := punctured_resolvent T i hi α R C D hα hR hC hD estimate z (hq.trans_le hz.2)
    refine ⟨Metric.ball z r, Metric.isOpen_ball, ?_⟩
    ext w
    constructor
    · intro hw
      have heq : w = z := by
        by_contra hn
        have hres := hball ⟨hw.1, by simpa only [mem_singleton_iff] using hn⟩
        exact hw.2.1 hres
      exact mem_singleton_iff.mpr heq
    · intro hw
      have heq := mem_singleton_iff.mp hw
      subst w
      exact ⟨Metric.mem_ball_self hr, hz⟩
  exact compact.finite discrete

end LeanShared.CompactTwoNormDiscreteSpectrum
