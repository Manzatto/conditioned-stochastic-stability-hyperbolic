module
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingAverages
public import LeanShared.Analysis.JensenPressureTangent
public import LeanShared.Analysis.WeightedExponentialJensen

/-! The pressure supporting inequality for the spectral product. For a deterministic leading record
with `A = λ⁻¹ P`, suppose the paired powers `ℓ(A^n p)` are the real orbit masses `Z n`, the
Birkhoff sums `Σ_{j<n} ℓ(A^j M A^{n-j} p)` are real masses `B n`, Jensen holds for the tilted
masses `Z_t n`, and these grow like `R^n` for every `R > e^c`. If the limit mass `m(p) ℓ(v)` has
positive real part, then `t · Re m(M v) ≤ c`. -/
public noncomputable section
open Filter Set Finset Real MeasureTheory
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem DeterministicLeading.pressure_tangent {P : E →L[ℂ] E} (d : DeterministicLeading P)
    (ℓ : E →L[ℂ] ℂ) (Mf : E →L[ℂ] E) (p : E) (Z Zt B : ℕ → ℝ)
    (hZ : ∀ n, ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p) = (Z n : ℂ))
    (hB : ∀ n, (∑ j ∈ range n,
      ℓ (((((d.rate : ℂ))⁻¹ • P) ^ j) (Mf (((((d.rate : ℂ))⁻¹ • P) ^ (n - j)) p)))) = (B n : ℂ))
    (ha : 0 < (d.mean p * ℓ d.vector).re) (t c : ℝ) (hZt : ∀ᶠ n in atTop, 0 < Zt n)
    (jensen : ∀ᶠ n in atTop, t * B n ≤ Z n * (log (Zt n) - log (Z n)))
    (growth : ∀ R, exp c < R → ∃ C, ∀ n, Zt n ≤ C * R ^ n) :
    t * (d.mean (Mf d.vector)).re ≤ c := by
  set a := d.mean p * ℓ d.vector
  have limitZ : Tendsto (fun n => (Z n : ℂ)) atTop (𝓝 a) := by
    have := d.power_limit ℓ p
    simp only [hZ] at this
    exact this
  have imZero : a.im = 0 := by
    have := (Complex.continuous_im.tendsto a).comp limitZ
    simp only [Function.comp_def, Complex.ofReal_im] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have realZ : Tendsto Z atTop (𝓝 a.re) := by
    have := (Complex.continuous_re.tendsto a).comp limitZ
    simpa only [Function.comp_def, Complex.ofReal_re] using this
  have limitB : Tendsto (fun n : ℕ => ((B n / n : ℝ) : ℂ)) atTop
      (𝓝 (ℓ d.vector * d.mean (Mf d.vector) * d.mean p)) := by
    have := d.average_limit ℓ Mf p
    simp only [hB] at this
    refine this.congr fun n => ?_
    push_cast
    rfl
  have product : (ℓ d.vector * d.mean (Mf d.vector) * d.mean p).re = a.re * (d.mean (Mf d.vector)).re := by
    have : ℓ d.vector * d.mean (Mf d.vector) * d.mean p = a * d.mean (Mf d.vector) := by
      simp only [a]; ring
    rw [this, Complex.mul_re, imZero, zero_mul, sub_zero]
  have realB : Tendsto (fun n : ℕ => B n / n) atTop (𝓝 (a.re * (d.mean (Mf d.vector)).re)) := by
    have := (Complex.continuous_re.tendsto _).comp limitB
    simp only [Function.comp_def, Complex.ofReal_re] at this
    rwa [product] at this
  exact LeanShared.JensenPressureTangent.tangent_of_jensen Z Zt B a.re _ t c ha realZ realB hZt
    jensen growth

/-- The limit mass of the paired normalized powers is positive when the paired raw powers grow at
every rate below the leading one along a shifted arithmetic progression. -/
theorem DeterministicLeading.mass_pos {P : E →L[ℂ] E} (d : DeterministicLeading P)
    (ℓ : E →L[ℂ] ℂ) (p : E) (Z : ℕ → ℝ) (hZnonneg : ∀ n, 0 ≤ Z n)
    (hZ : ∀ n, ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p) = (Z n : ℂ))
    (lower : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k → exp ((N * k : ℕ) * (log d.rate - δ)) ≤ C * ‖ℓ ((P ^ (N * k - 1)) p)‖) :
    0 < (d.mean p * ℓ d.vector).re := by
  set a := d.mean p * ℓ d.vector
  have limitZ : Tendsto (fun n => (Z n : ℂ)) atTop (𝓝 a) := by
    have := d.power_limit ℓ p
    simp only [hZ] at this
    exact this
  have imZero : a.im = 0 := by
    have := (Complex.continuous_im.tendsto a).comp limitZ
    simp only [Function.comp_def, Complex.ofReal_im] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have reNonneg : 0 ≤ a.re := by
    have := (Complex.continuous_re.tendsto a).comp limitZ
    simp only [Function.comp_def, Complex.ofReal_re] at this
    exact ge_of_tendsto' this hZnonneg
  rcases reNonneg.lt_or_eq with pos | zero
  · exact pos
  exfalso
  have aZero : a = 0 := Complex.ext zero.symm imZero
  obtain ⟨C, ϑ, hC, hϑ0, hϑ1, decay⟩ := d.decay
  set ϑ' := max ϑ (1 / 2)
  have hϑ'0 : 0 < ϑ' := lt_max_of_lt_right (by norm_num)
  have hϑ'1 : ϑ' < 1 := max_lt hϑ1 (by norm_num)
  have hϑϑ' : ϑ ≤ ϑ' := le_max_left _ _
  set δ := -log ϑ' / 2
  have logNeg : log ϑ' < 0 := log_neg hϑ'0 hϑ'1
  have hδ : 0 < δ := by simp only [δ]; linarith
  obtain ⟨N, hN, C', hC', bound⟩ := lower δ hδ
  have rate := d.rate_pos
  -- the paired normalized powers decay
  have small : ∀ n, ‖ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p)‖ ≤ ‖ℓ‖ * C * ‖p‖ * ϑ' ^ n := fun n => by
    have identity : ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p) =
        ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p - d.mean p • d.vector) := by
      rw [map_sub, map_smul, smul_eq_mul]
      change _ = _ - a
      rw [aZero, sub_zero]
    rw [identity]
    calc _ ≤ ‖ℓ‖ * (C * ϑ ^ n * ‖p‖) := (ℓ.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (decay n p) (norm_nonneg _))
      _ ≤ ‖ℓ‖ * (C * ϑ' ^ n * ‖p‖) := by gcongr
      _ = _ := by ring
  -- raw powers are the normalized ones times `λ^n`
  have raw : ∀ n, ‖ℓ ((P ^ n) p)‖ = d.rate ^ n * ‖ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p)‖ := fun n => by
    rw [smul_pow, smul_apply, map_smul, norm_smul, norm_pow, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg rate.le, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ rate.ne', one_pow, one_mul]
  -- growth of `(e^{-δ} / ϑ')^n`
  set K := C' * (‖ℓ‖ * C * ‖p‖) / (d.rate * ϑ')
  have ratio : 1 < exp (-δ) / ϑ' := by
    rw [one_lt_div hϑ'0]
    calc ϑ' = exp (log ϑ') := (exp_log hϑ'0).symm
      _ < exp (-δ) := exp_lt_exp.mpr (by simp only [δ]; linarith)
  obtain ⟨k0, hk0⟩ := pow_unbounded_of_one_lt K ratio
  have hk : 0 < k0 + 1 := Nat.succ_pos _
  have contra := bound (k0 + 1) hk
  set n := N * (k0 + 1)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hk.ne')
  rw [raw] at contra
  have upper : exp ((n : ℕ) * (log d.rate - δ)) ≤ C' * (d.rate ^ (n - 1) * (‖ℓ‖ * C * ‖p‖ * ϑ' ^ (n - 1))) :=
    contra.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (small _)
      (pow_nonneg rate.le _)) hC'.le)
  have left : exp ((n : ℕ) * (log d.rate - δ)) = d.rate ^ n * exp (-δ) ^ n := by
    rw [← exp_log rate, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, exp_log rate]
    · congr 1; ring
  have splitR : d.rate ^ n = d.rate ^ (n - 1) * d.rate := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have splitT : ϑ' ^ n = ϑ' ^ (n - 1) * ϑ' := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [left] at upper
  set A := ‖ℓ‖ * C * ‖p‖
  have h1 : d.rate * exp (-δ) ^ n ≤ C' * (A * ϑ' ^ (n - 1)) := by
    rw [splitR] at upper
    have hp : 0 < d.rate ^ (n - 1) := pow_pos rate _
    refine le_of_mul_le_mul_left ?_ hp
    calc d.rate ^ (n - 1) * (d.rate * exp (-δ) ^ n) = d.rate ^ (n - 1) * d.rate * exp (-δ) ^ n := by
          ring
      _ ≤ C' * (d.rate ^ (n - 1) * (A * ϑ' ^ (n - 1))) := upper
      _ = d.rate ^ (n - 1) * (C' * (A * ϑ' ^ (n - 1))) := by ring
  have Kform : K * ϑ' ^ n = C' * (A * ϑ' ^ (n - 1)) / d.rate := by
    simp only [K, A]
    rw [splitT]
    field_simp
  have key : (exp (-δ) / ϑ') ^ n ≤ K := by
    rw [div_pow, div_le_iff₀ (pow_pos hϑ'0 n), Kform, le_div_iff₀ rate]
    linarith
  have grow : K < (exp (-δ) / ϑ') ^ n := by
    calc K < (exp (-δ) / ϑ') ^ k0 := hk0
      _ ≤ (exp (-δ) / ϑ') ^ n := pow_le_pow_right₀ ratio.le
          (by simp only [n]; nlinarith [hN])
  linarith

/-- The pressure supporting inequality from orbit masses on a measure space. The normalized
paired powers and Birkhoff sums are integrals of a nonnegative weight `w n` and of `w n · S n`;
the paired raw powers grow at every rate below `e^{P0}` along a shifted progression, the tilted
masses grow like `R^n` for every `R > e^c`, and `|S n| ≤ n K`. -/
theorem DeterministicLeading.orbit_tangent {P : E →L[ℂ] E} (d : DeterministicLeading P)
    (ℓ : E →L[ℂ] ℂ) (Mf : E →L[ℂ] E) (p : E) {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (w S : ℕ → X → ℝ) (wNonneg : ∀ n x, 0 ≤ w n x) (wInt : ∀ n, Integrable (w n) ν)
    (wSInt : ∀ n (t : ℝ), Integrable (fun x => w n x * (t * S n x)) ν)
    (wExpInt : ∀ n (t : ℝ), Integrable (fun x => w n x * exp (t * S n x)) ν)
    (K : ℝ) (hS : ∀ n x, |S n x| ≤ n * K)
    (hZ : ∀ n, ℓ (((((d.rate : ℂ))⁻¹ • P) ^ n) p) = (((d.rate ^ n)⁻¹ * ∫ x, w n x ∂ν : ℝ) : ℂ))
    (hB : ∀ n, (∑ j ∈ range n,
      ℓ (((((d.rate : ℂ))⁻¹ • P) ^ j) (Mf (((((d.rate : ℂ))⁻¹ • P) ^ (n - j)) p)))) =
        (((d.rate ^ n)⁻¹ * ∫ x, w n x * S n x ∂ν : ℝ) : ℂ))
    (P0 : ℝ) (hrate : d.rate = exp P0)
    (lower : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k → exp ((N * k : ℕ) * (P0 - δ)) ≤ C * ‖ℓ ((P ^ (N * k - 1)) p)‖)
    (t c : ℝ)
    (growth : ∀ R, exp c < R → ∃ C, ∀ n, (d.rate ^ n)⁻¹ * ∫ x, w n x * exp (t * S n x) ∂ν ≤ C * R ^ n) :
    t * (d.mean (Mf d.vector)).re ≤ c := by
  have lamPos : 0 < d.rate := d.rate_pos
  let Z : ℕ → ℝ := fun n => (d.rate ^ n)⁻¹ * ∫ x, w n x ∂ν
  let B : ℕ → ℝ := fun n => (d.rate ^ n)⁻¹ * ∫ x, w n x * S n x ∂ν
  let Zt : ℕ → ℝ := fun n => (d.rate ^ n)⁻¹ * ∫ x, w n x * exp (t * S n x) ∂ν
  have ha : 0 < (d.mean p * ℓ d.vector).re :=
    d.mass_pos ℓ p Z (fun n => mul_nonneg (inv_nonneg.mpr (pow_nonneg lamPos.le n))
      (integral_nonneg (wNonneg n))) hZ (fun δ hδ => by
        obtain ⟨N, hN, C, hC, hbound⟩ := lower δ hδ
        refine ⟨N, hN, C, hC, fun k hk => ?_⟩
        rw [hrate, log_exp]
        exact hbound k hk)
  have limitZ : Tendsto Z atTop (𝓝 (d.mean p * ℓ d.vector).re) := by
    have := (Complex.continuous_re.tendsto _).comp (d.power_limit ℓ p)
    simp only [Function.comp_def, hZ, Complex.ofReal_re] at this
    exact this
  have Zpos : ∀ᶠ n in atTop, 0 < Z n := limitZ.eventually (lt_mem_nhds ha)
  have Ztpos : ∀ᶠ n in atTop, 0 < Zt n := by
    filter_upwards [Zpos] with n hn
    have cpos : 0 < (d.rate ^ n)⁻¹ := inv_pos.mpr (pow_pos lamPos n)
    have Wpos : 0 < ∫ x, w n x ∂ν := pos_of_mul_pos_right hn cpos.le
    have lowerBound : ∫ x, w n x * exp (-(|t| * (n * K))) ∂ν ≤ ∫ x, w n x * exp (t * S n x) ∂ν := by
      refine integral_mono ((wInt n).mul_const _) (wExpInt n t) fun x => ?_
      refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (wNonneg n x)
      have := neg_abs_le (t * S n x)
      rw [abs_mul] at this
      nlinarith [abs_nonneg t, hS n x]
    rw [integral_mul_const] at lowerBound
    exact mul_pos cpos (lt_of_lt_of_le (mul_pos Wpos (exp_pos _)) lowerBound)
  have jensen : ∀ᶠ n in atTop, t * B n ≤ Z n * (log (Zt n) - log (Z n)) := by
    filter_upwards [Zpos, Ztpos] with n hn hnt
    have cpos : 0 < (d.rate ^ n)⁻¹ := inv_pos.mpr (pow_pos lamPos n)
    have Wpos : 0 < ∫ x, w n x ∂ν := pos_of_mul_pos_right hn cpos.le
    have Ypos : 0 < ∫ x, w n x * exp (t * S n x) ∂ν := pos_of_mul_pos_right hnt cpos.le
    have J := LeanShared.WeightedExponentialJensen.jensen (w n) (fun x => t * S n x) (wNonneg n)
      (wInt n) (wSInt n t) (wExpInt n t) Wpos
    have e1 : t * B n = (d.rate ^ n)⁻¹ * ∫ x, w n x * (t * S n x) ∂ν := by
      have : (fun x => w n x * (t * S n x)) = fun x => t * (w n x * S n x) := by
        funext x
        ring
      simp only [B]
      rw [this, integral_const_mul]
      ring
    have e2 : log (Zt n) - log (Z n) =
        log (∫ x, w n x * exp (t * S n x) ∂ν) - log (∫ x, w n x ∂ν) := by
      simp only [Zt, Z]
      rw [log_mul cpos.ne' Ypos.ne', log_mul cpos.ne' Wpos.ne']
      ring
    rw [e1, e2]
    simp only [Z]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left J cpos.le
  exact d.pressure_tangent ℓ Mf p Z Zt B hZ hB ha t c Ztpos jensen growth

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
