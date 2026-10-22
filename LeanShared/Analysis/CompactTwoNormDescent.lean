module

public import LeanShared.Analysis.CompactTwoNormClosedRange
public import LeanShared.Analysis.CompactTwoNormFredholm
public import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Tactic.Linarith

/-! Stabilization of shifted ranges from compact weak inclusion and the actual
Lasota–Yorke estimate. No finite-descent or meromorphic-resolvent source is assumed. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.CompactTwoNormDescent
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [CompleteSpace E] in
/-- Closed shifted ranges and one contracting power force finite descent. -/
theorem finite_descent_of_power (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (μ : ℂ) (hμ : μ ≠ 0) (n : ℕ) (θ D : ℝ)
    (hθ : 0 ≤ θ) (hD : 0 ≤ D) (hgap : 6 * θ < ‖μ ^ n‖)
    (estimate : ∀ x, ‖(T ^ n) x‖ ≤ θ * ‖x‖ + D * ‖i x‖)
    (closed : ∀ k : ℕ, IsClosed (((T - μ • 1) ^ k).range : Set E)) :
    ∃ k : ℕ, ((T - μ • 1 : E →L[ℂ] E) ^ k).range =
      ((T - μ • 1 : E →L[ℂ] E) ^ (k + 1)).range := by
  classical
  let S := T - μ • (1 : E →L[ℂ] E)
  let V := fun k : ℕ => ((S : Module.End ℂ E) ^ k).range
  have decreasing : Antitone V := (S : Module.End ℂ E).iterateRange.monotone
  by_contra! never
  have separated (k : ℕ) : ∃ x : E, x ∈ V k ∧ ‖x‖ ≤ 3 ∧
      ∀ y ∈ V (k + 1), 1 ≤ ‖x - y‖ := by
    have witness : ∃ x : V k, x ∉ (V (k + 1)).comap (V k).subtype := by
      by_contra! h
      have back : V k ≤ V (k + 1) := fun x hx => h ⟨x, hx⟩
      have equal := le_antisymm back (decreasing (Nat.le_succ k))
      exact never k (by simpa only [← toLinearMap_pow] using (show ((S : Module.End ℂ E) ^ k).range = ((S : Module.End ℂ E) ^ (k + 1)).range from equal))
    have hc : IsClosed (V (k + 1) : Set E) := by
      simpa only [V, ← toLinearMap_pow] using closed (k + 1)
    have hclosed : IsClosed ((V (k + 1)).comap (V k).subtype : Set (V k)) := hc.preimage_val
    obtain ⟨⟨x, hx⟩, hnorm, hfar⟩ := riesz_lemma_of_norm_lt
      (show 1 < ‖(2 : ℂ)‖ by norm_num) (R := 3) (by norm_num) hclosed witness
    refine ⟨x, hx, hnorm, fun y hy => ?_⟩
    exact hfar ⟨y, decreasing (Nat.le_succ k) hy⟩ hy
  choose f hmem hupper hfar using separated
  obtain ⟨R, left, right⟩ := CompactTwoNormFredholm.power_factor T μ n
  have comm : Commute S R := by change S * R = R * S; exact left.trans right.symm
  let d (x : E) := (T ^ n) x - (μ ^ n) • x
  have dfactor (x : E) : d x = (S * R) x := by
    rw [left]
    rfl
  have mem {b a : ℕ} (hab : a ≤ b) : f b ∈ ((S : Module.End ℂ E) ^ a).range :=
    (S : Module.End ℂ E).iterateRange.monotone hab (hmem b)
  have dmem {b a : ℕ} (hab : a ≤ b) : d (f b) ∈
      ((S : Module.End ℂ E) ^ (a + 1)).range := by
    obtain ⟨v, hv⟩ := mem hab
    rw [← toLinearMap_pow] at hv
    change (S ^ a : E →L[ℂ] E) v = f b at hv
    refine ⟨R v, ?_⟩
    rw [← toLinearMap_pow]
    change (S ^ (a + 1) : E →L[ℂ] E) (R v) = d (f b)
    rw [← hv, dfactor, ← mul_apply_eq_comp, ← mul_apply_eq_comp]
    congr 1
    rw [mul_assoc, (comm.symm.pow_right a).eq, ← mul_assoc, ← pow_succ']
  have separated : Pairwise fun a b => ‖μ ^ n‖ ≤ ‖(T ^ n) (f a) - (T ^ n) (f b)‖ := by
    have : Std.Symm (fun a b => ‖μ ^ n‖ ≤ ‖(T ^ n) (f a) - (T ^ n) (f b)‖) := by
      constructor
      intro a b h
      simpa only [norm_sub_rev] using h
    apply Pairwise.of_lt
    intro a b hab
    let u := (μ ^ n)⁻¹ • (d (f b) - d (f a) + (μ ^ n) • f b)
    have hu : (μ ^ n) • (f a - u) = (T ^ n) (f a) - (T ^ n) (f b) := by
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero n hμ)]
      dsimp only [d]
      abel
    have umem : u ∈ ((S : Module.End ℂ E) ^ (a + 1)).range :=
      Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.sub_mem _ (dmem hab.le) (dmem le_rfl))
        (Submodule.smul_mem _ _ (mem hab)))
    grw [← hu, norm_smul, mul_comm, ← hfar a u umem, one_mul]
  obtain ⟨K, hK, hKi⟩ := hi.image_closedBall_subset_compact 3
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun a => hKi ⟨f a, by simpa using hupper a, rfl⟩)
  have hcauchy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  let ε := (‖μ ^ n‖ - 6 * θ) / (D + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hclose : ‖i (f (ψ (N + 1))) - i (f (ψ N))‖ < ε := by
    have hh := hN (N + 1) (Nat.le_succ N)
    simpa only [Function.comp_apply, coe_coe, dist_eq_norm_sub] using hh
  have hsep := separated (show ψ (N + 1) ≠ ψ N by simp [hψ.injective.eq_iff])
  have hnorm : ‖f (ψ (N + 1)) - f (ψ N)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith [hupper (ψ (N + 1)), hupper (ψ N)])
  have hest := estimate (f (ψ (N + 1)) - f (ψ N))
  rw [map_sub, map_sub] at hest
  have hθbound := mul_le_mul_of_nonneg_left hnorm hθ
  have hDclose := mul_le_mul_of_nonneg_left hclose.le hD
  have hεeq : ε * (D + 1) = ‖μ ^ n‖ - 6 * θ := div_mul_cancel₀ _ (by positivity)
  nlinarith


/-- Every spectral shift outside the strong growth disk has finite descent,
with all shifted ranges closed as a consequence of the same hypotheses. -/
theorem finite_descent (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (μ : ℂ) (hμ : α < ‖μ‖) :
    ∃ k : ℕ, ((T - μ • 1 : E →L[ℂ] E) ^ k).range =
      ((T - μ • 1 : E →L[ℂ] E) ^ (k + 1)).range := by
  have hμpos : 0 < ‖μ‖ := hα.trans_lt hμ
  have hμ0 : μ ≠ 0 := norm_pos_iff.mp hμpos
  have ratio : α / ‖μ‖ < 1 := (div_lt_one hμpos).mpr hμ
  have tend : Tendsto (fun n : ℕ => C * (α / ‖μ‖) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα hμpos.le) ratio).const_mul C
  obtain ⟨N, hN⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))).exists
  have hpower : 0 < ‖μ‖ ^ N := pow_pos hμpos N
  have hdivide : C * (α / ‖μ‖) ^ N = (C * α ^ N) / ‖μ‖ ^ N := by rw [div_pow]; ring
  rw [hdivide] at hN
  have hgap : 6 * (C * α ^ N) < ‖μ ^ N‖ := by
    rw [norm_pow]
    have hh := (div_lt_iff₀ hpower).mp hN
    nlinarith
  exact finite_descent_of_power T i hi μ hμ0 N (C * α ^ N) (D * R ^ N)
    (mul_nonneg hC (pow_nonneg hα N)) (mul_nonneg hD (pow_nonneg hR N)) hgap
    (estimate N)
    (CompactTwoNormClosedRange.spectral_shift T i hi α R C D hα hR hD estimate μ hμ).2

end LeanShared.CompactTwoNormDescent
