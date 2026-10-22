module

public import LeanShared.Analysis.SquareCompactFredholm
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Compact weak embeddings and two-norm estimates imply the Fredholm
alternative outside the strong growth disk. -/

public section

open Filter Topology Module ContinuousLinearMap

namespace LeanShared.CompactTwoNormFredholm

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Peetre's compactness argument for an injective operator. -/
theorem antilipschitz_of_compact_estimate (S : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (hinj : Function.Injective S)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (estimate : ∀ x, ‖x‖ ≤ A * ‖S x‖ + B * ‖i x‖) :
    ∃ K, AntilipschitzWith K S := by
  have pairBound : ∃ K, AntilipschitzWith K (S.prod i) := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    refine ⟨(A + B + 1)⁻¹, by positivity, fun x => ?_⟩
    have hs : ‖S x‖ ≤ ‖(S.prod i) x‖ := by simp only [prod_apply, Prod.norm_def]; exact le_max_left _ _
    have hw : ‖i x‖ ≤ ‖(S.prod i) x‖ := by simp only [prod_apply, Prod.norm_def]; exact le_max_right _ _
    have hh := estimate x
    have hn := norm_nonneg ((S.prod i) x)
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity : 0 < A + B + 1)]
    nlinarith
  obtain ⟨Kpair, hpair⟩ := pairBound
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  have small : ∀ ε > 0, ∃ x : X, ‖x‖ ≤ 1 ∧ (2 : ℝ)⁻¹ ≤ ‖x‖ ∧ ‖S x‖ < ε := by
    intro ε hε
    obtain ⟨x, hx⟩ := h ε hε
    have hxn : x ≠ 0 := by intro he; simp [he] at hx
    obtain ⟨a, _, hupper, hlower, _⟩ :=
      rescale_to_shell (show 1 < ‖(2 : ℂ)‖ by norm_num) (ε := 1) (by simp) hxn
    refine ⟨a • x, hupper.le, by simpa using hlower, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * hupper
  obtain ⟨φ, _, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose x hxupper hxlower hxsmall using fun n => small (φ n) (hφpos n)
  have hS : Tendsto (fun n => S (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  obtain ⟨K, hK, hKi⟩ := hi.image_closedBall_subset_compact 1
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKi ⟨x n, by simpa using hxupper n, rfl⟩)
  have hlim : Tendsto (fun n => (S.prod i) (x (ψ n))) atTop (𝓝 (0, y)) :=
    (hS.comp hψ.tendsto_atTop).prodMk_nhds hψy
  have hm : (0, y) ∈ Set.range (S.prod i) :=
    (hpair.isClosed_range (S.prod i).uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => ⟨x (ψ n), rfl⟩))
  obtain ⟨z, hz⟩ := hm
  have hSz : S z = 0 := congrArg Prod.fst hz
  have hz0 : z = 0 := hinj (by simpa using hSz)
  have hxlim : Tendsto (fun n => x (ψ n)) atTop (𝓝 z) :=
    (hpair.isEmbedding (S.prod i).continuous).tendsto_nhds_iff.mpr (by rw [hz]; exact hlim)
  have hn := ge_of_tendsto hxlim.norm (Eventually.of_forall (fun n => hxlower (ψ n)))
  rw [hz0, norm_zero] at hn
  norm_num at hn

omit [CompleteSpace X] in
/-- Both polynomial factorizations of a spectral power difference. -/
theorem power_factor (T : X →L[ℂ] X) (μ : ℂ) (n : ℕ) :
    ∃ R : X →L[ℂ] X,
      (T - μ • 1) * R = T ^ n - (μ ^ n) • 1 ∧
      R * (T - μ • 1) = T ^ n - (μ ^ n) • 1 := by
  let c : X →L[ℂ] X := algebraMap ℂ (X →L[ℂ] X) μ
  have comm : Commute T c := (Algebra.commutes μ T).symm
  refine ⟨∑ k ∈ Finset.range n, T ^ k * c ^ (n - 1 - k), ?_, ?_⟩
  · simpa only [c, Algebra.algebraMap_eq_smul_one, smul_pow, one_pow] using comm.mul_geom_sum₂ n
  · simpa only [c, Algebra.algebraMap_eq_smul_one, smul_pow, one_pow] using comm.geom_sum₂_mul n

/-- A single sufficiently contracting power estimate makes an injective shift
bounded below. -/
theorem antilipschitz_of_power_estimate (T : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (μ : ℂ) (n : ℕ) (θ D : ℝ)
    (hD : 0 ≤ D) (hθ : θ < ‖μ ^ n‖)
    (estimate : ∀ x, ‖(T ^ n) x‖ ≤ θ * ‖x‖ + D * ‖i x‖)
    (hinj : Function.Injective (T - μ • 1 : X →L[ℂ] X)) :
    ∃ K, AntilipschitzWith K (T - μ • 1 : X →L[ℂ] X) := by
  obtain ⟨R, _, right⟩ := power_factor T μ n
  have factor (x : X) : (T ^ n) x - (μ ^ n) • x = R ((T - μ • 1) x) := by
    have hh := congrArg (fun (Q : X →L[ℂ] X) => Q x) right
    simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh.symm
  have gap : 0 < ‖μ ^ n‖ - θ := sub_pos.mpr hθ
  apply antilipschitz_of_compact_estimate (T - μ • 1) i hi hinj
    (‖R‖ / (‖μ ^ n‖ - θ)) (D / (‖μ ^ n‖ - θ)) (by positivity) (by positivity)
  intro x
  have hn : ‖μ ^ n‖ * ‖x‖ ≤ ‖(T ^ n) x‖ + ‖(T ^ n) x - (μ ^ n) • x‖ := by
    simpa only [norm_smul] using norm_le_norm_add_norm_sub ((T ^ n) x) ((μ ^ n) • x)
  have herr : ‖(T ^ n) x - (μ ^ n) • x‖ ≤ ‖R‖ * ‖(T - μ • 1) x‖ := by
    rw [factor]
    exact R.le_opNorm _
  calc
    ‖x‖ ≤ (‖R‖ * ‖(T - μ • 1) x‖ + D * ‖i x‖) / (‖μ ^ n‖ - θ) :=
      (le_div_iff₀ gap).mpr (by nlinarith [estimate x])
    _ = _ := by ring

/-- One power whose strong coefficient is sufficiently small excludes residual
spectrum. Compactness is required only in the weaker norm. -/
theorem surjective_of_power_estimate (T : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (μ : ℂ) (hμ : μ ≠ 0) (n : ℕ) (θ D : ℝ)
    (hθ : 0 ≤ θ) (hD : 0 ≤ D) (hgap : 6 * θ < ‖μ ^ n‖)
    (estimate : ∀ x, ‖(T ^ n) x‖ ≤ θ * ‖x‖ + D * ‖i x‖)
    (hinj : Function.Injective (T - μ • 1 : X →L[ℂ] X)) :
    Function.Surjective (T - μ • 1 : X →L[ℂ] X) := by
  by_contra hsurj
  let S := T - μ • 1
  obtain ⟨Kbound, hbound⟩ := antilipschitz_of_power_estimate T i hi μ n θ D hD
    (by linarith) estimate hinj
  obtain ⟨f, _, hupper, hmem, hfar⟩ := IsCompactOperator.exists_seq hsurj
    (hbound.isClosedEmbedding S.uniformContinuous)
    (show 1 < ‖(2 : ℂ)‖ by norm_num) (R := 3) (by norm_num)
  obtain ⟨R, left, right⟩ := power_factor T μ n
  have comm : Commute S R := by change S * R = R * S; exact left.trans right.symm
  let d (x : X) := (T ^ n) x - (μ ^ n) • x
  have dfactor (x : X) : d x = (S * R) x := by
    rw [left]
    rfl
  have mem {b a : ℕ} (hab : a ≤ b) : f b ∈ ((S : Module.End ℂ X) ^ a).range :=
    (S : Module.End ℂ X).iterateRange.monotone hab (hmem b)
  have dmem {b a : ℕ} (hab : a ≤ b) : d (f b) ∈
      ((S : Module.End ℂ X) ^ (a + 1)).range := by
    obtain ⟨v, hv⟩ := mem hab
    rw [← toLinearMap_pow] at hv
    change (S ^ a : X →L[ℂ] X) v = f b at hv
    refine ⟨R v, ?_⟩
    rw [← toLinearMap_pow]
    change (S ^ (a + 1) : X →L[ℂ] X) (R v) = d (f b)
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
    have umem : u ∈ ((S : Module.End ℂ X) ^ (a + 1)).range :=
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

/-- Fredholm alternative above the strong growth rate from the all-power
two-norm inequality and a compact weak inclusion. No essential-radius theorem
or spectral contract is an input. -/
theorem surjective_of_twoNorm (T : X →L[ℂ] X) (i : X →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (μ : ℂ) (hμ : α < ‖μ‖)
    (hinj : Function.Injective (T - μ • 1 : X →L[ℂ] X)) :
    Function.Surjective (T - μ • 1 : X →L[ℂ] X) := by
  have hμpos : 0 < ‖μ‖ := hα.trans_lt hμ
  have hμ0 : μ ≠ 0 := norm_pos_iff.mp hμpos
  have ratio : α / ‖μ‖ < 1 := (div_lt_one hμpos).mpr hμ
  have tend := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα hμpos.le) ratio).const_mul C
  have tendZero : Tendsto (fun n : ℕ => C * (α / ‖μ‖) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tend
  have eventuallySmall : ∀ᶠ n : ℕ in atTop, C * (α / ‖μ‖) ^ n < 1 / 6 :=
    tendZero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))
  obtain ⟨n, hn⟩ := eventuallySmall.exists
  have hpower : 0 < ‖μ‖ ^ n := pow_pos hμpos n
  have hdivide : C * (α / ‖μ‖) ^ n = (C * α ^ n) / ‖μ‖ ^ n := by rw [div_pow]; ring
  rw [hdivide] at hn
  have hgap : 6 * (C * α ^ n) < ‖μ ^ n‖ := by
    rw [norm_pow]
    have hh := (div_lt_iff₀ hpower).mp hn
    nlinarith
  exact surjective_of_power_estimate T i hi μ hμ0 n (C * α ^ n) (D * R ^ n)
    (mul_nonneg hC (pow_nonneg hα n)) (mul_nonneg hD (pow_nonneg hR n)) hgap
    (estimate n) hinj

end LeanShared.CompactTwoNormFredholm
