module
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
public import LeanShared.Analysis.SpectralRadiusPowerBound
public import LeanShared.Analysis.ContinuousLinearMapPowApply

/-! Exponential convergence of normalized powers to the rank-one leading projector. For a
deterministic leading record of `P` with rate `λ`, vector `v` and mean `m`, there are `C ≥ 0`
and `0 ≤ ϑ < 1` with `‖(λ⁻¹ P)^n x - m(x) v‖ ≤ C ϑ^n ‖x‖`. The complementary operator `Q = P - λ
m ⊗ v` satisfies `m ∘ Q = 0`, hence `P^{n+1} = Q^{n+1} + λ^{n+1} m ⊗ v`, and its powers decay at
any rate above the subordinate radius. -/
public noncomputable section
open Filter Set
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem DeterministicLeading.decay {P : E →L[ℂ] E} (d : DeterministicLeading P) :
    ∃ C ϑ : ℝ, 0 ≤ C ∧ 0 ≤ ϑ ∧ ϑ < 1 ∧ ∀ (n : ℕ) (x : E),
      ‖((((d.rate : ℂ))⁻¹ • P) ^ n) x - d.mean x • d.vector‖ ≤ C * ϑ ^ n * ‖x‖ := by
  set lam := d.rate with hlam0
  have hlam : 0 < lam := d.rate_pos
  set Q := P - d.mean.smulRight ((lam : ℂ) • d.vector) with hQ
  have Qapply (y : E) : Q y = P y - (lam * d.mean y) • d.vector := by
    rw [hQ, sub_apply, ContinuousLinearMap.smulRight_apply, smul_smul,
      mul_comm]
  have meanQ (y : E) : d.mean (Q y) = 0 := by
    rw [Qapply, map_sub, map_smul, d.left_equation, d.normalization, smul_eq_mul, mul_one, sub_self]
  -- the power identity
  have power (n : ℕ) (x : E) :
      P^[n + 1] x = Q^[n + 1] x + ((lam : ℂ) ^ (n + 1) * d.mean x) • d.vector := by
    induction n with
    | zero =>
      simp only [zero_add, Function.iterate_one, pow_one, Qapply]
      abel
    | succ n ih =>
      have hP (y : E) : P y = Q y + (lam * d.mean y) • d.vector := by rw [Qapply]; abel
      have zero : d.mean (Q^[n + 1] x) = 0 := by
        rw [Function.iterate_succ_apply']
        exact meanQ _
      rw [Function.iterate_succ_apply', ih, map_add, map_smul, d.right_equation,
        hP (Q^[n + 1] x), zero, mul_zero, zero_smul, add_zero, ← Function.iterate_succ_apply' (⇑Q),
        smul_smul]
      congr 2
      rw [hlam0]
      ring
  -- geometric decay of the complementary powers
  set r := (d.subordinate + lam) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith [d.subordinate_nonneg]
  have hrlam : r < lam := by rw [hr]; linarith [d.subordinate_lt_rate]
  have radius : spectralRadius ℂ Q < ENNReal.ofReal r :=
    d.complementary_radius.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr0).mpr
      (by rw [hr]; linarith [d.subordinate_lt_rate]))
  obtain ⟨C, hC, bound⟩ := LeanShared.SpectralRadiusPowerBound.exists_geometric_bound Q r hr0 radius
  clear_value r lam
  set C0 := 1 + ‖d.mean‖ * ‖d.vector‖
  refine ⟨max C C0, r / lam, le_max_of_le_left hC.le, div_nonneg hr0.le hlam.le,
    (div_lt_one hlam).mpr hrlam, fun n x => ?_⟩
  have hϑ : 0 ≤ r / lam := div_nonneg hr0.le hlam.le
  rcases n with _ | n
  · simp only [pow_zero, one_apply_eq_self, mul_one]
    calc ‖x - d.mean x • d.vector‖ ≤ ‖x‖ + ‖d.mean x • d.vector‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖d.mean‖ * ‖x‖ * ‖d.vector‖ := by
          rw [norm_smul]
          gcongr
          exact d.mean.le_opNorm x
      _ = C0 * ‖x‖ := by ring
      _ ≤ max C C0 * ‖x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · have hpow : ((((lam : ℂ))⁻¹ • P) ^ (n + 1)) x = (((lam : ℂ))⁻¹ ^ (n + 1)) • P^[n + 1] x := by
      rw [smul_pow, smul_apply, LeanShared.ContinuousLinearMapPowApply.pow_apply]
    have hlamc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    have identity : ((((lam : ℂ))⁻¹ • P) ^ (n + 1)) x - d.mean x • d.vector =
        (((lam : ℂ))⁻¹ ^ (n + 1)) • Q^[n + 1] x := by
      rw [hpow, power, smul_add, smul_smul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hlamc, one_pow,
        one_mul]
      abel
    rw [identity, norm_smul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlam, ← LeanShared.ContinuousLinearMapPowApply.pow_apply]
    calc (lam⁻¹) ^ (n + 1) * ‖(Q ^ (n + 1)) x‖ ≤ (lam⁻¹) ^ (n + 1) * (C * r ^ (n + 1) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (((Q ^ (n + 1)).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (bound (n + 1)) (norm_nonneg _))) (by positivity)
      _ = C * (r / lam) ^ (n + 1) * ‖x‖ := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring
      _ ≤ max C C0 * (r / lam) ^ (n + 1) * ‖x‖ := by
          gcongr
          exact le_max_left _ _

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
