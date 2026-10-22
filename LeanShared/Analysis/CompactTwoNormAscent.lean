module

public import LeanShared.Analysis.CompactTwoNormFredholm
public import LeanShared.Analysis.CompactTwoNormEigenSpace
public import LeanShared.LinearAlgebra.FiniteKernelPowers
public import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Tactic.Linarith

/-! Stabilization of generalized kernels outside the strong growth disk.
The compact weak inclusion excludes arbitrarily long Jordan chains, using
Riesz-separated vectors and the actual two-norm estimate. -/

public section
open Filter Topology ContinuousLinearMap Set
namespace LeanShared.CompactTwoNormAscent
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [CompleteSpace E] in
/-- A contracting power estimate forces the generalized kernels to stabilize.
No compactness of the operator itself and no pole theorem are assumed. -/
theorem finite_ascent_of_power (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (μ : ℂ) (hμ : μ ≠ 0) (N : ℕ) (θ D : ℝ)
    (hθ : 0 ≤ θ) (hD : 0 ≤ D) (hgap : 6 * θ < ‖μ ^ N‖)
    (estimate : ∀ x, ‖(T ^ N) x‖ ≤ θ * ‖x‖ + D * ‖i x‖) :
    ∃ n : ℕ, ((T - μ • 1 : E →L[ℂ] E) ^ n).ker = ((T - μ • 1 : E →L[ℂ] E) ^ (n + 1)).ker := by
  classical
  let S := T - μ • (1 : E →L[ℂ] E)
  let V := fun n : ℕ => (S ^ n).ker
  have increasing : Monotone V := by
    apply monotone_nat_of_le_succ
    intro n x hx
    change (S ^ n) x = 0 at hx
    change (S ^ (n + 1)) x = 0
    rw [pow_succ', mul_apply_eq_comp, hx, map_zero]
  by_contra! never
  have separated (n : ℕ) : ∃ x : E, x ∈ V (n + 1) ∧ ‖x‖ ≤ 3 ∧
      ∀ y ∈ V n, 1 ≤ ‖x - y‖ := by
    have witness : ∃ x : V (n + 1), x ∉ (V n).comap (V (n + 1)).subtype := by
      by_contra! h
      have back : V (n + 1) ≤ V n := fun x hx => h ⟨x, hx⟩
      exact never n (le_antisymm (increasing (Nat.le_succ n)) back)
    have closed : IsClosed ((V n).comap (V (n + 1)).subtype : Set (V (n + 1))) :=
      (S ^ n).isClosed_ker.preimage_val
    obtain ⟨⟨x, hx⟩, hnorm, hfar⟩ := riesz_lemma_of_norm_lt
      (show 1 < ‖(2 : ℂ)‖ by norm_num) (R := 3) (by norm_num) closed witness
    refine ⟨x, hx, hnorm, fun y hy => ?_⟩
    exact hfar ⟨y, increasing (Nat.le_succ n) hy⟩ hy
  choose f hf hupper hfar using separated
  obtain ⟨P, left, right⟩ := CompactTwoNormFredholm.power_factor T μ N
  have comm : Commute S P := by change S * P = P * S; exact left.trans right.symm
  let d := fun x : E => (T ^ N) x - (μ ^ N) • x
  have dmem (n : ℕ) : d (f n) ∈ V n := by
    have hfn : (S ^ (n + 1)) (f n) = 0 := hf n
    have factor : d (f n) = (S * P) (f n) := by rw [left]; rfl
    change (S ^ n) (d (f n)) = 0
    rw [factor, ← mul_apply_eq_comp, ← mul_assoc, ← pow_succ,
      (comm.pow_left (n + 1)).eq, mul_apply_eq_comp, hfn, map_zero]
  have Tmem {m n : ℕ} (hmn : m < n) : (T ^ N) (f m) ∈ V n := by
    have hd : d (f m) ∈ V n := increasing hmn.le (dmem m)
    have hf' : f m ∈ V n := increasing (Nat.succ_le_of_lt hmn) (hf m)
    have hh := Submodule.add_mem (V n) hd (Submodule.smul_mem (V n) (μ ^ N) hf')
    simpa only [d, sub_add_cancel] using hh
  have separation : Pairwise fun m n => ‖μ ^ N‖ ≤ ‖(T ^ N) (f m) - (T ^ N) (f n)‖ := by
    have : Std.Symm (fun m n => ‖μ ^ N‖ ≤ ‖(T ^ N) (f m) - (T ^ N) (f n)‖) := by
      constructor
      intro m n h
      simpa only [norm_sub_rev] using h
    apply Pairwise.of_lt
    intro m n hmn
    let u := (μ ^ N)⁻¹ • ((T ^ N) (f m) - d (f n))
    have hu : u ∈ V n := Submodule.smul_mem (V n) _
      (Submodule.sub_mem (V n) (Tmem hmn) (dmem n))
    have equation : (μ ^ N) • (f n - u) = (T ^ N) (f n) - (T ^ N) (f m) := by
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero N hμ)]
      dsimp only [d]
      abel
    have hh := mul_le_mul_of_nonneg_left (hfar n u hu) (norm_nonneg (μ ^ N))
    rw [mul_one, ← norm_smul, equation, norm_sub_rev] at hh
    exact hh
  obtain ⟨K, hK, hKi⟩ := hi.image_closedBall_subset_compact 3
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKi ⟨f n, by simpa using hupper n, rfl⟩)
  have hcauchy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  let ε := (‖μ ^ N‖ - 6 * θ) / (D + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨n, hn⟩ := hcauchy ε hε
  have hclose : ‖i (f (ψ (n + 1))) - i (f (ψ n))‖ < ε := by
    have hh := hn (n + 1) (Nat.le_succ n)
    simpa only [Function.comp_apply, coe_coe, dist_eq_norm_sub] using hh
  have hsep := separation (show ψ (n + 1) ≠ ψ n by simp [hψ.injective.eq_iff])
  have hnorm : ‖f (ψ (n + 1)) - f (ψ n)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith [hupper (ψ (n + 1)), hupper (ψ n)])
  have hest := estimate (f (ψ (n + 1)) - f (ψ n))
  rw [map_sub, map_sub] at hest
  have hθbound := mul_le_mul_of_nonneg_left hnorm hθ
  have hDclose := mul_le_mul_of_nonneg_left hclose.le hD
  have hεeq : ε * (D + 1) = ‖μ ^ N‖ - 6 * θ := div_mul_cancel₀ _ (by positivity)
  nlinarith


omit [CompleteSpace E] in
/-- The all-power Lasota–Yorke estimate gives finite ascent at every spectral
value outside the strong growth disk. -/
theorem finite_ascent (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (μ : ℂ) (hμ : α < ‖μ‖) :
    ∃ n : ℕ, ((T - μ • 1 : E →L[ℂ] E) ^ n).ker = ((T - μ • 1 : E →L[ℂ] E) ^ (n + 1)).ker := by
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
  exact finite_ascent_of_power T i hi μ hμ0 N (C * α ^ N) (D * R ^ N)
    (mul_nonneg hC (pow_nonneg hα N)) (mul_nonneg hD (pow_nonneg hR N)) hgap
    (estimate N)

/-- The full generalized spectral kernel stabilizes in one finite-dimensional
Jordan level, derived entirely from compactness and the two-norm estimate. -/
theorem finite_stable_generalized_kernel (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (μ : ℂ) (hμ : α < ‖μ‖) :
    ∃ n : ℕ, FiniteDimensional ℂ ((T - μ • 1 : E →L[ℂ] E) ^ n).ker ∧
      ∀ m : ℕ, ((T - μ • 1 : E →L[ℂ] E) ^ (n + m)).ker =
        ((T - μ • 1 : E →L[ℂ] E) ^ n).ker := by
  let S := T - μ • (1 : E →L[ℂ] E)
  obtain ⟨n, hn⟩ := finite_ascent T i hi α R C D hα hR hC hD estimate μ hμ
  have first : FiniteDimensional ℂ S.ker :=
    CompactTwoNormEigenSpace.finiteDimensional_spectralKernel T i hi α R C D hα hR hD estimate μ hμ
  let _ : FiniteDimensional ℂ (S : Module.End ℂ E).ker := first
  have hnLinear : ((S : Module.End ℂ E) ^ n).ker = ((S : Module.End ℂ E) ^ (n + 1)).ker := by
    simpa only [← toLinearMap_pow] using hn
  refine ⟨n, ?_, fun m => ?_⟩
  · have finite := FiniteKernelPowers.finiteDimensional (S : Module.End ℂ E) n
    have equality : ((S : Module.End ℂ E) ^ n).ker = (S ^ n).ker :=
      congrArg LinearMap.ker (toLinearMap_pow S n).symm
    rw [equality] at finite
    exact finite
  · have stable := Module.End.ker_pow_constant hnLinear m
    simpa only [← toLinearMap_pow] using stable.symm

end LeanShared.CompactTwoNormAscent
