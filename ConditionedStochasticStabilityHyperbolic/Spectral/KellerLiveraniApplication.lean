module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic
import Mathlib.Tactic.Linarith

/-!
# Deducing noisy leading spectral separation from KL projector outputs

Spectral confinement and rank preservation, rather than an assumed noisy
spectral gap, produce dominance, peripheral exclusion and simplicity. Conjugation of the actual analytic operator proves the nearby leading value
is real and positive. These deductions can fill the analytic fields of the
checked compared local QEM package.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

open KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- The leading branch remains above the comparison cutoff. -/
theorem ProjectorOutputs.eigenvalue_norm_gt
    (o : ProjectorOutputs P i d q δ) (hδ : δ < d.rate - q)
    (ε : ℝ≥0) (hε : ε ≤ o.window) : q < ‖o.eigenvalue ε‖ := by
  have hn := o.eigenvalue_near ε hε
  rw [dist_eq_norm] at hn
  have htriangle : d.rate ≤ ‖o.eigenvalue ε‖ + ‖o.eigenvalue ε - (d.rate : ℂ)‖ := by
    have ht := norm_sub_le (o.eigenvalue ε) (o.eigenvalue ε - (d.rate : ℂ))
    simpa only [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg d.rate_pos.le,
      norm_neg] using ht
  linarith

/-- Rank-one factorization fixes its normalized generating vector. -/
theorem ProjectorOutputs.project_vector
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0) (hε : ε ≤ o.window) :
    o.projection ε (o.vector ε) = o.vector ε := by
  rw [o.rank_one ε hε, ContinuousLinearMap.smulRight_apply, o.normalization ε hε, one_smul]

/-- The generating vector is a genuine leading eigenvector. -/
theorem ProjectorOutputs.right_equation
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0) (hε : ε ≤ o.window) :
    P ε (o.vector ε) = o.eigenvalue ε • o.vector ε := by
  have he := congrArg (fun T : E →L[ℂ] E => T (o.vector ε)) (o.eigen_action ε hε)
  simpa only [mul_apply_eq_comp, smul_apply, o.project_vector ε hε] using he

/-- Spectral confinement places every eigenvalue above the cutoff in the
leading disk, where the Riesz projector acts as the identity. -/
theorem ProjectorOutputs.eigenvalue_eq_of_above_cutoff [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδ : δ < q - d.subordinate)
    (ε : ℝ≥0) (hε : ε ≤ o.window) (x : E) (hx : x ≠ 0)
    (z : ℂ) (he : P ε x = z • x) (hz : q < ‖z‖) : z = o.eigenvalue ε := by
  have hmem : z ∈ spectrum ℂ (P ε) := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      (⟨Module.End.mem_eigenspace_iff.mpr he, hx⟩ :
        Module.End.HasEigenvector (P ε : Module.End ℂ E) z x)).mem_spectrum
  have hnear : dist z (d.rate : ℂ) ≤ δ := by
    obtain hsmall | ⟨w, hw, hzw⟩ := o.spectral_confinement ε hε z hmem
    · exact False.elim ((not_le_of_gt hz) hsmall)
    · obtain hlead | hsub := d.spectral_separation w hw
      · simpa only [hlead] using hzw
      · have ht : ‖z‖ ≤ dist z w + ‖w‖ := by
          simpa only [sub_add_cancel, dist_eq_norm] using norm_add_le (z - w) w
        have hle : ‖z‖ < q := by linarith
        exact False.elim ((not_lt_of_ge hz.le) hle)
  have hpx := o.project_eigenvector ε hε z hnear x he
  have hact := congrArg (fun T : E →L[ℂ] E => T x) (o.eigen_action ε hε)
  simp only [mul_apply_eq_comp, smul_apply, hpx, he] at hact
  exact (smul_left_injective ℂ hx) hact

/-- No noisy eigenvalue has larger modulus than the leading branch. -/
theorem ProjectorOutputs.eigenvalue_bound [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (x : E) (hx : x ≠ 0) (z : ℂ) (he : P ε x = z • x) :
    ‖z‖ ≤ ‖o.eigenvalue ε‖ := by
  by_cases hz : q < ‖z‖
  · rw [o.eigenvalue_eq_of_above_cutoff hδsub ε hε x hx z he hz]
  · exact (le_of_not_gt hz).trans (o.eigenvalue_norm_gt hδlead ε hε).le

/-- Peripheral cycles are excluded by the single rank-one Riesz subspace. -/
theorem ProjectorOutputs.peripheral_exclusion [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (x : E) (hx : x ≠ 0) (z : ℂ) (he : P ε x = z • x)
    (hz : ‖z‖ = ‖o.eigenvalue ε‖) : z = o.eigenvalue ε := by
  apply o.eigenvalue_eq_of_above_cutoff hδsub ε hε x hx z he
  rw [hz]
  exact o.eigenvalue_norm_gt hδlead ε hε

/-- Simplicity is derived from rank preservation, not assumed for noise. -/
theorem ProjectorOutputs.leading_simple
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (x : E) (he : P ε x = o.eigenvalue ε • x) :
    ∃ c : ℂ, x = c • o.vector ε := by
  have hp := o.project_eigenvector ε hε (o.eigenvalue ε)
    (o.eigenvalue_near ε hε).le x he
  rw [o.rank_one ε hε, ContinuousLinearMap.smulRight_apply] at hp
  exact ⟨o.mean ε x, hp.symm⟩

/-- Real operator realization on the analytic space, expressed by the
actual conjugation on distributions. This is independent of its spectrum. -/
structure RealOperatorConjugation (Q : E →L[ℂ] E) where
  conjugate : E → E
  involutive : Function.Involutive conjugate
  zero : conjugate 0 = 0
  smul : ∀ (c : ℂ) x, conjugate (c • x) = star c • conjugate x
  commute : ∀ x, Q (conjugate x) = conjugate (Q x)

/-- Uniqueness in the leading disk and real conjugation make the branch real. -/
theorem ProjectorOutputs.eigenvalue_real [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) :
    (o.eigenvalue ε).im = 0 := by
  have hx : o.vector ε ≠ 0 := by
    intro hz
    have he := o.normalization ε hε
    rw [hz, map_zero] at he
    exact zero_ne_one he
  have hcx : c.conjugate (o.vector ε) ≠ 0 := by
    intro hz
    apply hx
    have he := congrArg c.conjugate hz
    rw [c.involutive _, c.zero] at he
    exact he
  have he : P ε (c.conjugate (o.vector ε)) =
      star (o.eigenvalue ε) • c.conjugate (o.vector ε) := by
    rw [c.commute, o.right_equation ε hε, c.smul]
  have hz := o.eigenvalue_eq_of_above_cutoff hδsub ε hε
    (c.conjugate (o.vector ε)) hcx (star (o.eigenvalue ε)) he
    (by simpa only [norm_star] using o.eigenvalue_norm_gt hδlead ε hε)
  have him := congrArg Complex.im hz
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- The real branch stays positive and above the chosen cutoff. -/
theorem ProjectorOutputs.eigenvalue_re_gt
    (o : ProjectorOutputs P i d q δ) (hδlead : δ < d.rate - q)
    (ε : ℝ≥0) (hε : ε ≤ o.window) : q < (o.eigenvalue ε).re := by
  have hn := o.eigenvalue_near ε hε
  rw [dist_eq_norm] at hn
  have hnorm := Complex.abs_re_le_norm (o.eigenvalue ε - (d.rate : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hnorm
  have hleft := (neg_le_abs ((o.eigenvalue ε).re - d.rate)).trans hnorm
  linarith

/-- The source branch is exactly the embedding of its positive real part. -/
theorem ProjectorOutputs.eigenvalue_eq_real [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) :
    o.eigenvalue ε = ((o.eigenvalue ε).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using o.eigenvalue_real hδsub hδlead ε hε c

/-- Undoing operator scaling transports its eigenvector equation exactly. -/
theorem eigenvector_of_scaled_operator (Q : E →L[ℂ] E) (scale : ℝ) (hscale : 0 < scale)
    (x : E) (z : ℂ) (he : ((scale : ℂ) • Q) x = z • x) :
    Q x = ((scale : ℂ)⁻¹ * z) • x := by
  have hs : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hscale.ne'
  have h := congrArg (fun v : E => (scale : ℂ)⁻¹ • v) he
  simpa only [smul_apply, inv_smul_smul₀ hs, smul_smul] using h

/-- Positive raw scaling preserves the derived analytic dominant bound. -/
theorem ProjectorOutputs.raw_eigenvalue_bound [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (x : E) (hx : x ≠ 0) (z : ℂ) (he : ((scale : ℂ) • P ε) x = z • x) :
    ‖z‖ ≤ scale * (o.eigenvalue ε).re := by
  have hz := o.eigenvalue_bound hδsub hδlead ε hε x hx
    ((scale : ℂ)⁻¹ * z) (eigenvector_of_scaled_operator _ scale hscale x z he)
  rw [o.eigenvalue_eq_real hδsub hδlead ε hε c, Complex.norm_real,
    Real.norm_of_nonneg (hq.trans (o.eigenvalue_re_gt hδlead ε hε)).le,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hscale.le] at hz
  have hd : ‖z‖ / scale ≤ (o.eigenvalue ε).re := by
    simpa only [div_eq_mul_inv, mul_comm] using hz
  simpa only [mul_comm] using (div_le_iff₀ hscale).mp hd

/-- Raw peripheral exclusion follows from the normalized rank-one branch. -/
theorem ProjectorOutputs.raw_peripheral_exclusion [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (x : E) (hx : x ≠ 0) (z : ℂ) (he : ((scale : ℂ) • P ε) x = z • x)
    (hz : ‖z‖ = scale * (o.eigenvalue ε).re) :
    z = ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) := by
  have hnorm : ‖(scale : ℂ)⁻¹ * z‖ = ‖o.eigenvalue ε‖ := by
    rw [o.eigenvalue_eq_real hδsub hδlead ε hε c, Complex.norm_real,
      Real.norm_of_nonneg (hq.trans (o.eigenvalue_re_gt hδlead ε hε)).le,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hscale.le, hz]
    rw [← mul_assoc, inv_mul_cancel₀ hscale.ne', one_mul]
  have heq := o.peripheral_exclusion hδsub hδlead ε hε x hx
    ((scale : ℂ)⁻¹ * z) (eigenvector_of_scaled_operator _ scale hscale x z he) hnorm
  have hm := congrArg (fun a : ℂ => (scale : ℂ) * a) heq
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hscale.ne'), one_mul,
    o.eigenvalue_eq_real hδsub hδlead ε hε c, ← Complex.ofReal_mul] at hm
  exact hm

/-- The raw leading eigenspace is still the same one-dimensional space. -/
theorem ProjectorOutputs.raw_leading_simple [CompleteSpace E]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (x : E) (he : ((scale : ℂ) • P ε) x =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) • x) :
    ∃ a : ℂ, x = a • o.vector ε := by
  apply o.leading_simple ε hε x
  have h := eigenvector_of_scaled_operator _ scale hscale x _ he
  rw [Complex.ofReal_mul, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hscale.ne'), one_mul] at h
  rwa [o.eigenvalue_eq_real hδsub hδlead ε hε c]

/-- Fill the compared local interface from actual KL outputs. The analytic
noisy bound, peripheral exclusion and simplicity are all proved above and
are not supplied independently. Actual cross-space realizations of the
leading continuous pair remain classical spectral-comparison inputs. -/
def ProjectorOutputs.toComparedRawInputs [CompleteSpace E]
    {Y Z : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C) (R : ℝ)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z) (hb : Function.Injective b)
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ))
    (hcompact : IsCompactOperator
      (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
        (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ)))
    (hcompare : ComparedSpectralGap.EigenvectorComparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b (scale * q))
    (g : Y →ᵇ ℝ) (μ : (Y →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (Y →ᵇ ℂ) →L[ℂ] ℂ)
    (hident : b (AbsorbingMarkovChains.ComplexKernel.ofReal g) = a (o.vector ε))
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) * ℓ f) :
    ComparedLocalQuasiErgodic.ComparedRawSpectralInputs (A := E) (W := Z) C hSF R where
  analyticOperator := (scale : ℂ) • P ε
  analyticEmbedding := a
  continuousEmbedding := b
  embedding_injective := hb
  cutoff := scale * q
  rate := scale * (o.eigenvalue ε).re
  cutoff_lt_rate := mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale
  rate_pos := mul_pos hscale (hq.trans (o.eigenvalue_re_gt hδlead ε hε))
  fredholm := hFredholm
  square_compact := hcompact
  comparison := hcompare
  analyticVector := o.vector ε
  eigenvector := g
  mean := μ
  complexMean := ℓ
  vector_identification := hident
  real_compatibility := hreal
  normalization := hpair
  mean_one_pos := hmass
  right_equation := hright
  left_equation := hleft
  eigenvalue_bound := o.raw_eigenvalue_bound hδsub hδlead hq ε hε c scale hscale
  peripheral_exclusion := o.raw_peripheral_exclusion hδsub hδlead hq ε hε c scale hscale
  leading_simple := o.raw_leading_simple hδsub hδlead ε hε c scale hscale

/-- The deterministic leading rate cannot exceed the weak growth rate.
This comparison is derived from the actual eigenvector and weak estimate. -/
theorem DeterministicLeading.rate_le_weakRate
    (h : Hypotheses P i) (d : DeterministicLeading (P 0)) : d.rate ≤ h.weakRate := by
  have hv : d.vector ≠ 0 := by
    intro hz
    have hp := d.normalization
    rw [hz, map_zero] at hp
    exact zero_ne_one hp
  have hi : i d.vector ≠ 0 := by
    intro hz
    apply hv
    exact h.weak_injective (hz.trans (map_zero i).symm)
  have hip : 0 < ‖i d.vector‖ := norm_pos_iff.mpr hi
  have hM : 0 < h.weakRate := h.alpha_pos.trans h.alpha_lt_weakRate
  have hp (n : ℕ) : (P 0 ^ n) d.vector = ((d.rate : ℂ) ^ n) • d.vector := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, d.right_equation, smul_smul, pow_succ]
  have hbound (n : ℕ) : (d.rate / h.weakRate) ^ n ≤ h.weakConstant := by
    have hw := h.weak_growth 0 (by positivity) n d.vector
    rw [hp, map_smul, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg d.rate_pos.le] at hw
    have hn : d.rate ^ n ≤ h.weakConstant * h.weakRate ^ n :=
      (mul_le_mul_iff_left₀ hip).mp hw
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hM n)).mpr hn
  by_contra hn
  have hratio : 1 < d.rate / h.weakRate := (one_lt_div hM).mpr (lt_of_not_ge hn)
  obtain ⟨n, hnb⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hratio).eventually
    (eventually_gt_atTop h.weakConstant)).exists
  exact (not_lt_of_ge (hbound n)) hnb

/-- Choose an admissible contour cutoff and disk radius from the actual
spectral margins, then apply the precise deferred source theorem. -/
theorem exists_projector_outputs [CompleteSpace E]
    (hKL : ClassicalContract (E := E) (W := W)) (h : Hypotheses P i)
    (d : DeterministicLeading (P 0)) (hα : h.alpha < d.rate) :
    ∃ q δ : ℝ, 0 < q ∧ h.alpha < q ∧ d.subordinate < q ∧ q < d.rate ∧
      q < h.weakRate ∧ 0 < δ ∧ δ < q - d.subordinate ∧ δ < d.rate - q ∧
      Nonempty (ProjectorOutputs P i d q δ) := by
  let m := max h.alpha d.subordinate
  have hm : m < d.rate := max_lt hα d.subordinate_lt_rate
  let q := (m + d.rate) / 2
  have hmq : m < q := by dsimp only [q]; linarith
  have hqr : q < d.rate := by dsimp only [q]; linarith
  have hαq : h.alpha < q := (le_max_left _ _).trans_lt hmq
  have hsubq : d.subordinate < q := (le_max_right _ _).trans_lt hmq
  have hqM : q < h.weakRate := hqr.trans_le (d.rate_le_weakRate h)
  let gap := min (q - d.subordinate) (d.rate - q)
  have hgap : 0 < gap := lt_min (sub_pos.mpr hsubq) (sub_pos.mpr hqr)
  let δ := gap / 2
  have hδ : 0 < δ := div_pos hgap (by norm_num)
  have hδgap : δ < gap := by dsimp only [δ]; linarith
  have hδsub : δ < q - d.subordinate := hδgap.trans_le (min_le_left _ _)
  have hδlead : δ < d.rate - q := hδgap.trans_le (min_le_right _ _)
  refine ⟨q, δ, h.alpha_pos.trans hαq, hαq, hsubq, hqr, hqM, hδ, hδsub, hδlead, ?_⟩
  exact hKL P i h d q δ hαq hqr hqM hsubq hδ hδsub hδlead

/-- The intermediate-space projector bound used by product convergence is
also a consequence of the source weak projector convergence and coercivity. -/
theorem ProjectorOutputs.eventually_norm_projection_le
    (o : ProjectorOutputs P i d q δ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ‖o.projection ε‖ ≤
      o.coercivityConstant * (‖i.comp (o.projection 0)‖ + 1) := by
  have hε : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ o.window :=
    ((gt_mem_nhds o.window_pos) : {ε : ℝ≥0 | ε < o.window} ∈ 𝓝 0).mono
      (fun _ he => he.le)
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ‖i.comp (o.projection ε - o.projection 0)‖ ≤ 1 := by
    have hs := o.projector_convergence.norm.eventually (gt_mem_nhds (show ‖(0 : E →L[ℂ] W)‖ < 1 by simp))
    exact hs.mono (fun _ he => he.le)
  filter_upwards [hε, hsmall] with ε he hs
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg o.coercivityConstant_nonneg (by positivity))
  intro x
  have hdecomp : i (o.projection ε x) =
      (i.comp (o.projection 0)) x + (i.comp (o.projection ε - o.projection 0)) x := by
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    abel
  calc
    ‖o.projection ε x‖ ≤ o.coercivityConstant * ‖i (o.projection ε x)‖ := o.range_coercivity ε he x
    _ ≤ o.coercivityConstant * ((‖i.comp (o.projection 0)‖ + 1) * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ o.coercivityConstant_nonneg
      rw [hdecomp]
      calc
        _ ≤ ‖(i.comp (o.projection 0)) x‖ + ‖(i.comp (o.projection ε - o.projection 0)) x‖ := norm_add_le _ _
        _ ≤ ‖i.comp (o.projection 0)‖ * ‖x‖ + 1 * ‖x‖ :=
          add_le_add ((i.comp (o.projection 0)).le_opNorm x)
            (((i.comp (o.projection ε - o.projection 0)).le_opNorm x).trans
              (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
        _ = _ := by ring
    _ = _ := by ring

/-- The paper's chosen right branch `Pi_e gamma_0` converges in the actual
weak norm directly from the source projector convergence. -/
theorem ProjectorOutputs.projected_vector_weak_convergence
    (o : ProjectorOutputs P i d q δ) :
    Tendsto (fun ε => i (o.projection ε d.vector)) (𝓝 (0 : ℝ≥0)) (𝓝 (i d.vector)) := by
  have h := (ContinuousLinearMap.apply ℂ W d.vector).continuous.continuousAt.tendsto.comp
    o.projector_convergence
  have hp : o.projection 0 d.vector = d.vector := by
    rw [o.projection_zero, ContinuousLinearMap.smulRight_apply, d.normalization, one_smul]
  have hlim := h.add_const (i d.vector)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply, sub_apply, map_sub, hp, sub_add_cancel,
    zero_apply, zero_add] using hlim

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
