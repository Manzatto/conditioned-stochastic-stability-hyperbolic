module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement

/-! Deterministic cited leading data may be supplied on the actual raw
generator. Positive normalization constructs all data for the analytic
operator internally, without mentioning a produced noisy pair in the public
classical-source interface. -/

public noncomputable section
open Set
open scoped Pointwise
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem spectrum_scaled
    (P : E →L[ℂ] E) (c : ℝ) (hc : 0 < c) :
    spectrum ℂ ((c : ℂ) • P) = (c : ℂ) • spectrum ℂ P := by
  have h : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  simpa only [Units.smul_def, Units.val_mk0] using
    spectrum.unit_smul_eq_smul P (Units.mk0 (c : ℂ) h)

private theorem radius_scaled_bound
    (P : E →L[ℂ] E) (c : ℝ) (hc : 0 < c) (r : ℝ) (hr : 0 ≤ r)
    (radius : spectralRadius ℂ P ≤ ENNReal.ofReal r) :
    spectralRadius ℂ ((c : ℂ) • P) ≤ ENNReal.ofReal (c * r) := by
  rw [spectralRadius_eq_of_unital]
  apply iSup₂_le
  intro z hz
  rw [spectrum_scaled P c hc] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  change ‖(c : ℂ) * v‖ ≤ c * r
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  exact mul_le_mul_of_nonneg_left
    (norm_mem_spectrum_le_of_radius_le P r hr radius hv) hc.le

@[expose] def DeterministicLeading.rescale {P : E →L[ℂ] E}
    (d : DeterministicLeading P) (c : ℝ) (hc : 0 < c) :
    DeterministicLeading ((c : ℂ) • P) where
  rate := c * d.rate
  rate_pos := mul_pos hc d.rate_pos
  subordinate := c * d.subordinate
  subordinate_nonneg := mul_nonneg hc.le d.subordinate_nonneg
  subordinate_lt_rate := mul_lt_mul_of_pos_left d.subordinate_lt_rate hc
  vector := d.vector
  mean := d.mean
  normalization := d.normalization
  right_equation := by
    simp only [smul_apply, d.right_equation, smul_smul,
      Complex.ofReal_mul]
  left_equation := by
    intro x
    simp only [smul_apply, map_smul, smul_eq_mul,
      d.left_equation, Complex.ofReal_mul, mul_assoc]
  complementary_radius := by
    have eq : (c : ℂ) • P - d.mean.smulRight (((c * d.rate : ℝ) : ℂ) • d.vector) =
        (c : ℂ) • (P - d.mean.smulRight ((d.rate : ℂ) • d.vector)) := by
      ext x
      simp only [sub_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, Complex.ofReal_mul, smul_sub, mul_smul]
      rw [smul_comm (d.mean x) (c : ℂ)]
    rw [eq]
    exact radius_scaled_bound _ c hc d.subordinate d.subordinate_nonneg d.complementary_radius
  spectral_separation := by
    intro z hz
    rw [spectrum_scaled P c hc] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    obtain lead | small := d.spectral_separation v hv
    · left
      simp only [lead, smul_eq_mul, Complex.ofReal_mul]
    · right
      change ‖(c : ℂ) * v‖ ≤ c * d.subordinate
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      exact mul_le_mul_of_nonneg_left small hc.le
  leading_simple := by
    intro x hx
    apply d.leading_simple x
    apply smul_right_injective E (Complex.ofReal_ne_zero.mpr hc.ne')
    simpa only [smul_apply, Complex.ofReal_mul, mul_smul] using hx

@[simp] theorem DeterministicLeading.rescale_rate {P : E →L[ℂ] E}
    (d : DeterministicLeading P) (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).rate = c * d.rate := rfl

@[simp] theorem DeterministicLeading.rescale_vector {P : E →L[ℂ] E}
    (d : DeterministicLeading P) (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).vector = d.vector := rfl

@[simp] theorem DeterministicLeading.rescale_mean {P : E →L[ℂ] E}
    (d : DeterministicLeading P) (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).mean = d.mean := rfl

@[expose] def DeterministicLeading.transport {P Q : E →L[ℂ] E}
    (d : DeterministicLeading P) (eq : P = Q) : DeterministicLeading Q := eq ▸ d

@[simp] theorem DeterministicLeading.transport_rate {P Q : E →L[ℂ] E}
    (d : DeterministicLeading P) (eq : P = Q) :
    (d.transport eq).rate = d.rate := by subst Q; rfl

@[simp] theorem DeterministicLeading.transport_vector {P Q : E →L[ℂ] E}
    (d : DeterministicLeading P) (eq : P = Q) :
    (d.transport eq).vector = d.vector := by subst Q; rfl

@[simp] theorem DeterministicLeading.transport_mean {P Q : E →L[ℂ] E}
    (d : DeterministicLeading P) (eq : P = Q) :
    (d.transport eq).mean = d.mean := by subst Q; rfl

/-- Normalize the deterministic raw generator using the already proved
actual raw-zero identity, with no produced-pair value in the source type. -/
@[expose] def DeterministicLeading.normalizeOfRaw {P Q : E →L[ℂ] E}
    (d : DeterministicLeading Q) (R : ℝ) (hR : 0 < R)
    (raw : (R : ℂ) • P = Q) : DeterministicLeading P :=
  (d.rescale R⁻¹ (inv_pos.mpr hR)).transport (by
    rw [← raw, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hR.ne',
      Complex.ofReal_one, one_smul])

@[simp] theorem DeterministicLeading.normalizeOfRaw_rate {P Q : E →L[ℂ] E}
    (d : DeterministicLeading Q) (R : ℝ) (hR : 0 < R)
    (raw : (R : ℂ) • P = Q) :
    (d.normalizeOfRaw R hR raw).rate = R⁻¹ * d.rate := by
  simp only [normalizeOfRaw, transport_rate, rescale_rate]

@[simp] theorem DeterministicLeading.normalizeOfRaw_vector {P Q : E →L[ℂ] E}
    (d : DeterministicLeading Q) (R : ℝ) (hR : 0 < R)
    (raw : (R : ℂ) • P = Q) :
    (d.normalizeOfRaw R hR raw).vector = d.vector := by
  simp only [normalizeOfRaw, transport_vector, rescale_vector]

@[simp] theorem DeterministicLeading.normalizeOfRaw_mean {P Q : E →L[ℂ] E}
    (d : DeterministicLeading Q) (R : ℝ) (hR : 0 < R)
    (raw : (R : ℂ) • P = Q) :
    (d.normalizeOfRaw R hR raw).mean = d.mean := by
  simp only [normalizeOfRaw, transport_mean, rescale_mean]

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
