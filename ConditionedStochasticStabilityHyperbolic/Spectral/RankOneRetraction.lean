module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-! Descending a genuine rank-one power gap along an intertwining retraction.
This is the operator step in stabilization by an independent auxiliary saddle;
the retraction and its positivity must be constructed from the actual kernels.
-/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {P : E →L[ℝ] E} {Q : F →L[ℝ] F} {oneE : E} {oneF : F}
  (d : RankOneSpectralData Q oneF)
  (a : E →L[ℝ] F) (b : F →L[ℝ] E)
  (hba : b.comp a = ContinuousLinearMap.id ℝ E)
  (ha : Q.comp a = a.comp P) (hb : b.comp Q = P.comp b)

include hba ha hb in
private theorem lifted_eigenvector (hmean : 0 < d.mean (a oneE)) :
    a (b d.eigenvector) = d.eigenvector := by
  have hQa (x : E) : Q (a x) = a (P x) := congrArg (fun L : E →L[ℝ] F => L x) ha
  have hbQ (y : F) : b (Q y) = P (b y) := congrArg (fun L : F →L[ℝ] E => L y) hb
  have hba' (x : E) : b (a x) = x := congrArg (fun L : E →L[ℝ] E => L x) hba
  have comm (y : F) : Q (a (b y)) = a (b (Q y)) := by rw [hQa, hbQ]
  let l := d.mean.comp (a.comp b)
  have hl (y : F) : l (Q y) = d.rate * l y := by
    change d.mean (a (b (Q y))) = d.rate * d.mean (a (b y))
    rw [← comm, d.left_eigenfunctional]
  have hlEq := d.leading_eigenfunctional_eq l hl
  have hc := congrArg (fun L : F →L[ℝ] ℝ => L (a oneE)) hlEq
  change d.mean (a (b (a oneE))) = l d.eigenvector * d.mean (a oneE) at hc
  rw [hba'] at hc
  have hcoeff : l d.eigenvector = 1 := by nlinarith [hmean]
  have heigen : Q (a (b d.eigenvector)) = d.rate • a (b d.eigenvector) := by
    rw [comm, d.right_eigenvector, map_smul, map_smul]
  have he := d.leading_eigenvector_eq (a (b d.eigenvector)) heigen
  change a (b d.eigenvector) = l d.eigenvector • d.eigenvector at he
  simpa only [hcoeff, one_smul] using he

/-- The descended gap keeps the leading rate and geometric decay. The error
constant changes by the norms of the two constructed intertwiners. -/
def retract (hmean : 0 < d.mean (a oneE)) : RankOneSpectralData P oneE where
  rate := d.rate
  rate_pos := d.rate_pos
  mean := d.mean.comp a
  eigenvector := b d.eigenvector
  mean_eigenvector := by
    change d.mean (a (b d.eigenvector)) = 1
    rw [d.lifted_eigenvector a b hba ha hb hmean, d.mean_eigenvector]
  mean_one_pos := hmean
  right_eigenvector := by
    have h := congrArg (fun L : F →L[ℝ] E => L d.eigenvector) hb
    change b (Q d.eigenvector) = P (b d.eigenvector) at h
    rw [d.right_eigenvector, map_smul] at h
    exact h.symm
  errorConstant := ‖b‖ * d.errorConstant * ‖a‖
  errorConstant_nonneg := mul_nonneg (mul_nonneg (norm_nonneg _) d.errorConstant_nonneg)
    (norm_nonneg _)
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    intro n
    let PN := d.rate⁻¹ • P
    let QN := d.rate⁻¹ • Q
    have hstep (x : E) : QN (a x) = a (PN x) := by
      have h := congrArg (fun L : E →L[ℝ] F => L x) ha
      change Q (a x) = a (P x) at h
      simp only [QN, PN, smul_apply, h, map_smul]
    have hp (k : ℕ) (x : E) : (QN ^ k) (a x) = a ((PN ^ k) x) := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, hstep, pow_succ', mul_apply_eq_comp]
    have hcomp : b.comp ((QN ^ n).comp a) = PN ^ n := by
      ext x
      change b ((QN ^ n) (a x)) = (PN ^ n) x
      rw [hp]
      exact congrArg (fun L : E →L[ℝ] E => L ((PN ^ n) x)) hba
    have hproj : b.comp ((d.mean.smulRight d.eigenvector).comp a) =
        (d.mean.comp a).smulRight (b d.eigenvector) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul]
    have herror : PN ^ n - (d.mean.comp a).smulRight (b d.eigenvector) =
        b.comp ((QN ^ n - d.mean.smulRight d.eigenvector).comp a) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hcomp, hproj]
    change ‖PN ^ n - (d.mean.comp a).smulRight (b d.eigenvector)‖ ≤ _
    rw [herror]
    calc
      _ ≤ ‖b‖ * ‖(QN ^ n - d.mean.smulRight d.eigenvector).comp a‖ :=
        b.opNorm_comp_le _
      _ ≤ ‖b‖ * (‖QN ^ n - d.mean.smulRight d.eigenvector‖ * ‖a‖) :=
        mul_le_mul_of_nonneg_left ((QN ^ n - d.mean.smulRight d.eigenvector).opNorm_comp_le a)
          (norm_nonneg _)
      _ ≤ ‖b‖ * ((d.errorConstant * d.decay ^ n) * ‖a‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (d.power_gap n) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring

/-- The leading vector actually lies in the lifted factor. -/
theorem retract_lift_eigenvector (hmean : 0 < d.mean (a oneE)) :
    a ((d.retract a b hba ha hb hmean).eigenvector) = d.eigenvector :=
  d.lifted_eigenvector a b hba ha hb hmean

@[simp] theorem retract_rate (hmean : 0 < d.mean (a oneE)) :
    (d.retract a b hba ha hb hmean).rate = d.rate := rfl

@[simp] theorem retract_eigenvector (hmean : 0 < d.mean (a oneE)) :
    (d.retract a b hba ha hb hmean).eigenvector = b d.eigenvector := rfl

@[simp] theorem retract_mean (hmean : 0 < d.mean (a oneE)) :
    (d.retract a b hba ha hb hmean).mean = d.mean.comp a := rfl

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData
