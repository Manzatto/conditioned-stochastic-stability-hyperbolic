module
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
public import LeanShared.Analysis.RankOneRieszProjection
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Linarith

/-! Every circle within the stated deterministic gap has the literal rank-one
Riesz projector. Its radius is arbitrary within that gap, not an extra source. -/
public section
open Set Metric ContinuousLinearMap Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem DeterministicLeading.projection_relations {T : E →L[ℂ] E}
    (d : DeterministicLeading T) :
    (d.mean.smulRight d.vector)*(d.mean.smulRight d.vector)=d.mean.smulRight d.vector ∧
    T*(d.mean.smulRight d.vector)=(d.rate : ℂ)•d.mean.smulRight d.vector ∧
    (d.mean.smulRight d.vector)*T=(d.rate : ℂ)•d.mean.smulRight d.vector := by
  constructor
  · ext x
    simp only [mul_apply_eq_comp,smulRight_apply,map_smul,d.normalization,one_smul]
  constructor
  · ext x
    simp only [mul_apply_eq_comp,smulRight_apply,map_smul,d.right_equation,smul_apply,smul_smul]
    rw [mul_comm]
  · ext x
    simp only [mul_apply_eq_comp,smulRight_apply,d.left_equation,smul_apply,smul_smul]

theorem DeterministicLeading.riesz_circle {T : E →L[ℂ] E}
    (d : DeterministicLeading T) (r : ℝ) (hr : 0 < r)
    (gap : r < d.rate-d.subordinate) :
    (0 : ℂ) ∉ closedBall (d.rate : ℂ) r ∧
    (closedBall (d.rate : ℂ) r \ {(d.rate : ℂ)} ⊆ resolventSet ℂ T) ∧
    LeanShared.RieszContourIdempotent.projector T (d.rate : ℂ) r=d.mean.smulRight d.vector := by
  let p := d.mean.smulRight d.vector
  have normRate : ‖(d.rate : ℂ)‖=d.rate := by simp [abs_of_pos d.rate_pos]
  have lower : ∀ z ∈ closedBall (d.rate : ℂ) r, d.subordinate < ‖z‖ := by
    intro z hz
    have bound := norm_sub_norm_le (d.rate : ℂ) z
    rw [normRate,← dist_eq_norm,dist_comm] at bound
    change dist z (d.rate : ℂ) ≤ r at hz
    linarith
  have excludes : (0 : ℂ) ∉ closedBall (d.rate : ℂ) r := by
    intro hh
    have impossible := lower 0 hh
    simp only [norm_zero] at impossible
    exact (not_lt_of_ge d.subordinate_nonneg) impossible
  have remainder : T-(d.rate : ℂ)•p=T-d.mean.smulRight ((d.rate : ℂ)•d.vector) := by
    congr 1
    ext x
    simp only [p,smul_apply,smulRight_apply,smul_smul]
    rw [mul_comm]
  have complement : ∀ z ∈ closedBall (d.rate : ℂ) r,
      z ∈ resolventSet ℂ (T-(d.rate : ℂ)•p) := by
    intro z hz
    apply spectrum.mem_resolventSet_of_spectralRadius_lt
    rw [remainder]
    apply d.complementary_radius.trans_lt
    exact (ENNReal.ofReal_lt_coe_iff d.subordinate_nonneg).mpr (lower z hz)
  have relations := d.projection_relations
  have disk : closedBall (d.rate : ℂ) r \ {(d.rate : ℂ)} ⊆ resolventSet ℂ T := by
    intro z hz
    exact (LeanShared.RankOneResolvent.formula T p (d.rate : ℂ) z relations.1
      relations.2.1 relations.2.2 (by intro he; subst z; exact excludes hz.1)
      hz.2 (complement z hz.1)).1
  refine ⟨excludes,disk,?_⟩
  exact LeanShared.RankOneResolvent.circle_integral_eq T p (d.rate : ℂ) r hr disk
    (LeanShared.RankOneResolvent.residue T p (d.rate : ℂ)
      (by exact_mod_cast ne_of_gt d.rate_pos) relations.1 relations.2.1 relations.2.2
      (complement (d.rate : ℂ) (mem_closedBall_self hr.le)))
end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
