module

public import LeanShared.Analysis.ResolventNeumannSeries
public import LeanShared.Analysis.AnalyticResolvent
public import LeanShared.Analysis.MeromorphicIdentity
public import LeanShared.Analysis.MeromorphicLinearMap
public import LeanShared.Analysis.ExteriorConnected
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Scalar coefficient growth constructs a genuine analytic resolvent
pairing beyond the coefficient growth disk, even when the full operator
norm is larger. Meromorphic continuation then identifies it with the
actual resolvent at every resolvent point in that exterior region. -/

@[expose] public noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ENNReal NNReal

namespace LeanShared.ScalarCoefficientResolvent

variable (c : ℕ → ℂ) (C R : ℝ) (positive : 0 < R)
  (growth : ∀ n, ‖c n‖ ≤ C * R ^ n)

include positive growth in
theorem radius_lower : ENNReal.ofReal R⁻¹ ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  let r : ℝ≥0 := ⟨R⁻¹, inv_nonneg.mpr positive.le⟩
  have h := (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_bound C (r := r) (fun n => by
    rw [FormalMultilinearSeries.ofScalars_norm]
    change ‖c n‖ * (R⁻¹) ^ n ≤ C
    calc
      ‖c n‖ * (R⁻¹) ^ n ≤ (C * R ^ n) * (R⁻¹) ^ n :=
        mul_le_mul_of_nonneg_right (growth n) (pow_nonneg (inv_nonneg.mpr positive.le) n)
      _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ positive.ne', one_pow, mul_one])
  convert h using 1
  exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr positive.le)

include positive growth in
theorem inverse_mem_ball (z : ℂ) (outside : R < ‖z‖) :
    z⁻¹ ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  have large : 0 < ‖z‖ := positive.trans outside
  have norm_lt : ‖z⁻¹‖ < R⁻¹ := by
    rw [norm_inv]
    exact inv_lt_inv₀ large positive |>.mpr outside
  change edist z⁻¹ 0 < _
  rw [edist_dist, dist_zero_right]
  exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr positive)).mpr norm_lt |>.trans_le
    (radius_lower c C R positive growth)

/-- The scalar resolvent supplied by the actual coefficient series. -/
def value (z : ℂ) : ℂ := z⁻¹ * FormalMultilinearSeries.ofScalarsSum c z⁻¹

include positive growth in
theorem hasSum_value (z : ℂ) (outside : R < ‖z‖) :
    HasSum (fun n => z⁻¹ * (c n * (z⁻¹) ^ n)) (value c z) := by
  have h := (FormalMultilinearSeries.ofScalars ℂ c).hasSum
    (inverse_mem_ball c C R positive growth z outside)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    value, FormalMultilinearSeries.ofScalarsSum] using h.mul_left z⁻¹

include positive growth in
theorem analyticAt_value (z : ℂ) (outside : R < ‖z‖) : AnalyticAt ℂ (value c) z := by
  have radiusPositive : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr positive)).trans_le (radius_lower c C R positive growth)
  have series := ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall radiusPositive).analyticAt_of_mem
    (inverse_mem_ball c C R positive growth z outside)
  have invAnalytic : AnalyticAt ℂ (fun w : ℂ => w⁻¹) z :=
    analyticAt_inv (norm_pos_iff.mp (positive.trans outside))
  exact invAnalytic.mul (series.comp invAnalytic)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (P : H →L[ℂ] H) (ℓ : H →L[ℂ] ℂ) (x : H)

/-- Outer Neumann expansion identifies the constructed scalar function. -/
theorem eq_outer (C R : ℝ) (positive : 0 < R)
    (growth : ∀ n, ‖ℓ ((P ^ n) x)‖ ≤ C * R ^ n)
    (z : ℂ) (outside : R < ‖z‖) (outer : ‖P‖ < ‖z‖) :
    ℓ ((resolvent P z) x) = value (fun n => ℓ ((P ^ n) x)) z := by
  have actual := (ResolventNeumannSeries.hasSum P z outer).mapL
    (ℓ.comp (ContinuousLinearMap.apply ℂ H x))
  have scalar := hasSum_value (fun n => ℓ ((P ^ n) x)) C R positive growth z outside
  apply actual.unique
  convert scalar using 1
  funext n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    smul_pow, map_smul, smul_eq_mul]
  ring

/-- Meromorphy propagates the exact pairing from the outer Neumann region
to every actual resolvent point outside the coefficient growth disk. -/
theorem eq_on_resolvent (C R : ℝ) (positive : 0 < R)
    (growth : ∀ n, ‖ℓ ((P ^ n) x)‖ ≤ C * R ^ n)
    (meromorphic : MeromorphicOn (resolvent P) {z : ℂ | R < ‖z‖})
    (z : ℂ) (outside : R < ‖z‖) (regular : z ∈ resolventSet ℂ P) :
    ℓ ((resolvent P z) x) = value (fun n => ℓ ((P ^ n) x)) z := by
  let w : ℂ := ((‖P‖ + R + 1 : ℝ) : ℂ)
  have normW : ‖w‖ = ‖P‖ + R + 1 := by
    simp only [w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [norm_nonneg P] : 0 < ‖P‖ + R + 1)]
  have outW : R < ‖w‖ := by rw [normW]; linarith [norm_nonneg P]
  have outerW : ‖P‖ < ‖w‖ := by rw [normW]; linarith
  have mf : MeromorphicOn (fun z => ℓ ((resolvent P z) x)) {z : ℂ | R < ‖z‖} :=
    fun z hz => MeromorphicLinearMap.map (ℓ.comp (ContinuousLinearMap.apply ℂ H x))
      (meromorphic z hz)
  have mg : MeromorphicOn (value (fun n => ℓ ((P ^ n) x))) {z : ℂ | R < ‖z‖} :=
    fun z hz => (analyticAt_value _ C R positive growth z hz).meromorphicAt
  have near : (fun z => ℓ ((resolvent P z) x)) =ᶠ[𝓝 w]
      value (fun n => ℓ ((P ^ n) x)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds outW,
      (isOpen_lt continuous_const continuous_norm).mem_nhds outerW] with z hz ho
    exact eq_outer P ℓ x C R positive growth z hz ho
  exact MeromorphicIdentity.eq_of_eventuallyEq mf mg
    (ExteriorConnected.isPreconnected (E := ℂ) (by simp [Complex.rank_real_complex]) positive.le)
    outW near outside
    (((ℓ.comp (ContinuousLinearMap.apply ℂ H x)).analyticAt _).comp
      (AnalyticResolvent.analyticAt P regular)).continuousAt
    (analyticAt_value _ C R positive growth z outside).continuousAt

end LeanShared.ScalarCoefficientResolvent
