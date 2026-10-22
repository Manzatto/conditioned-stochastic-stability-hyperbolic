module
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingDecay
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingRescale

/-! Uniqueness of the deterministic leading data. Two leading records of one operator have the same
rate, proportional vectors and inversely proportional means, so the product functional
`m(M v)` and the ratio `m(M w) / m(w)` for any leading eigenvector `w` are intrinsic. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Filter Set
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem mem_spectrum_of_eigenvector (P : E →L[ℂ] E) (c : ℂ) (v : E) (hv : v ≠ 0)
    (h : P v = c • v) : c ∈ spectrum ℂ P := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have h0 : (u : E →L[ℂ] E) v = 0 := by
    rw [hu, Algebra.algebraMap_eq_smul_one, sub_apply, smul_apply, h]
    simp
  have back : ((↑u⁻¹ : E →L[ℂ] E) * ↑u) v = v := by rw [Units.inv_mul]; rfl
  change (↑u⁻¹ : E →L[ℂ] E) ((u : E →L[ℂ] E) v) = v at back
  rw [h0, map_zero] at back
  exact hv back.symm

theorem DeterministicLeading.vector_ne_zero {P : E →L[ℂ] E} (d : DeterministicLeading P) :
    d.vector ≠ 0 := fun h => by
  have := d.normalization
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem DeterministicLeading.rate_eq {P : E →L[ℂ] E} (d d' : DeterministicLeading P) :
    d.rate = d'.rate := by
  have h1 := mem_spectrum_of_eigenvector P _ _ d'.vector_ne_zero d'.right_equation
  have h2 := mem_spectrum_of_eigenvector P _ _ d.vector_ne_zero d.right_equation
  have norm1 : ‖(d'.rate : ℂ)‖ = d'.rate := by
    rw [Complex.norm_real, Real.norm_of_nonneg d'.rate_pos.le]
  have norm2 : ‖(d.rate : ℂ)‖ = d.rate := by
    rw [Complex.norm_real, Real.norm_of_nonneg d.rate_pos.le]
  rcases d.spectral_separation _ h1 with e | le
  · exact (Complex.ofReal_injective e).symm
  rcases d'.spectral_separation _ h2 with e' | le'
  · exact Complex.ofReal_injective e'
  rw [norm1] at le
  rw [norm2] at le'
  linarith [d.subordinate_lt_rate, d'.subordinate_lt_rate]

/-- A leading eigenvector is the mean multiple of the leading vector. -/
theorem DeterministicLeading.eigenvector_eq {P : E →L[ℂ] E} (d : DeterministicLeading P) (w : E)
    (hw : P w = (d.rate : ℂ) • w) : w = d.mean w • d.vector := by
  obtain ⟨c, hc⟩ := d.leading_simple w hw
  have : d.mean w = c := by rw [hc, map_smul, d.normalization, smul_eq_mul, mul_one]
  rw [this]
  exact hc

theorem DeterministicLeading.power_tendsto {P : E →L[ℂ] E} (d : DeterministicLeading P) (x : E) :
    Tendsto (fun n : ℕ => ((((d.rate : ℂ))⁻¹ • P) ^ n) x) atTop (𝓝 (d.mean x • d.vector)) := by
  obtain ⟨C, ϑ, hC, hϑ0, hϑ1, decay⟩ := d.decay
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have small : Tendsto (fun n : ℕ => C * ϑ ^ n * ‖x‖) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hϑ0 hϑ1).const_mul C).mul_const ‖x‖
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => decay n x) small

theorem DeterministicLeading.mean_eq {P : E →L[ℂ] E} (d d' : DeterministicLeading P) (x : E) :
    d.mean x = d'.mean x * d.mean d'.vector := by
  have rate := d.rate_eq d'
  have vec := d.eigenvector_eq d'.vector (by rw [rate]; exact d'.right_equation)
  have lim1 := d.power_tendsto x
  have lim2 := d'.power_tendsto x
  rw [← rate] at lim2
  have same := tendsto_nhds_unique lim1 lim2
  rw [vec, smul_smul] at same
  have := congrArg d.mean same
  rwa [map_smul, map_smul, d.normalization, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at this

/-- The product functional of a leading record is intrinsic. -/
theorem DeterministicLeading.product_eq {P : E →L[ℂ] E} (d d' : DeterministicLeading P)
    (M : E →L[ℂ] E) : d'.mean (M d'.vector) = d.mean (M d.vector) := by
  have rate := d.rate_eq d'
  have vec := d.eigenvector_eq d'.vector (by rw [rate]; exact d'.right_equation)
  set c := d.mean d'.vector
  have hc : c ≠ 0 := fun h => d'.vector_ne_zero (by rw [vec, h, zero_smul])
  have means := d.mean_eq d' (M d.vector)
  rw [vec, map_smul, map_smul, smul_eq_mul, means]
  ring

/-- The leading ratio is intrinsic: `m(M w) / m(w) = m(M v)` for every leading eigenvector `w ≠ 0`. -/
theorem DeterministicLeading.ratio_eq {P : E →L[ℂ] E} (d : DeterministicLeading P) (M : E →L[ℂ] E)
    (w : E) (hw : P w = (d.rate : ℂ) • w) (hw0 : w ≠ 0) :
    d.mean (M w) / d.mean w = d.mean (M d.vector) := by
  have vec := d.eigenvector_eq w hw
  set c := d.mean w with hcdef
  have hc : c ≠ 0 := fun h => hw0 (by rw [vec, h, zero_smul])
  have num : d.mean (M w) = c * d.mean (M d.vector) := by
    conv_lhs => rw [vec]
    rw [map_smul, map_smul, smul_eq_mul]
  rw [num]
  field_simp

/-- The consumer ratio of two compatible leading records is the intrinsic product functional. -/
theorem DeterministicLeading.compatible_ratio {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
    [CompleteSpace S] (i : S →L[ℂ] E) (hi : Function.Injective i) (PS : S →L[ℂ] S) (PH : E →L[ℂ] E)
    (hcomp : i.comp PS = PH.comp i) (ds : DeterministicLeading PS) (dm : DeterministicLeading PH)
    (hrate : ds.rate = dm.rate) (d : DeterministicLeading PH) (M : E →L[ℂ] E) :
    dm.mean (M (i ds.vector)) / dm.mean (i ds.vector) = d.mean (M d.vector) := by
  have eig : PH (i ds.vector) = (dm.rate : ℂ) • i ds.vector := by
    have := congrArg (fun L : S →L[ℂ] E => L ds.vector) hcomp
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this, ds.right_equation, map_smul, hrate]
  have ne : i ds.vector ≠ 0 := fun h => ds.vector_ne_zero (hi (h.trans (map_zero i).symm))
  rw [dm.ratio_eq M _ eig ne, d.product_eq dm M]

/-- The consumer ratio of normalized compatible leading records equals the raw product value. -/
theorem DeterministicLeading.ratio_of_raw {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
    [CompleteSpace S] {Q : E →L[ℂ] E} (d : DeterministicLeading Q) (R : ℝ) (hR : 0 < R)
    (PH : E →L[ℂ] E) (raw : (R : ℂ) • PH = Q) (i : S →L[ℂ] E) (hi : Function.Injective i)
    (PS : S →L[ℂ] S) (hcomp : i.comp PS = PH.comp i) (ds : DeterministicLeading PS)
    (dm : DeterministicLeading PH) (hrate : ds.rate = dm.rate) (M : E →L[ℂ] E) (value : ℝ)
    (hvalue : (d.mean (M d.vector)).re = value) :
    (dm.mean (M (i ds.vector)) / dm.mean (i ds.vector)).re = value := by
  rw [DeterministicLeading.compatible_ratio i hi PS PH hcomp ds dm hrate
    (d.normalizeOfRaw R hR raw) M, DeterministicLeading.normalizeOfRaw_mean,
    DeterministicLeading.normalizeOfRaw_vector]
  exact hvalue

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
