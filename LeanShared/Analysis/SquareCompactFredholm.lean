module

public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import all Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Tactic.LinearCombination

/-! Fredholm alternative for operators with compact square. The proof uses
compactness only for T²; no spectral/Fredholm theorem is assumed for T. -/

public section

open Module Filter Topology
open ContinuousLinearMap

namespace LeanShared.SquareCompactFredholm

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- An injective nonzero shift of an operator with compact square is bounded below. -/
theorem antilipschitz_shift (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    {μ : 𝕜} (hμ : μ ≠ 0)
    (hinj : Function.Injective (T - μ • 1 : X →L[𝕜] X)) :
    ∃ K, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
  have small : ∀ ε > 0, ∃ x : X, ‖x‖ ≤ 1 ∧ ‖C‖⁻¹ ≤ ‖x‖ ∧
      ‖(T - μ • 1) x‖ < ε := by
    intro ε hε
    obtain ⟨x, hx⟩ := h ε hε
    have hxn : x ≠ 0 := by intro he; simp [he] at hx
    obtain ⟨a, ha, hupper, hlower, _⟩ :=
      rescale_to_shell hC (ε := 1) (by simp) hxn
    refine ⟨a • x, hupper.le, by simpa using hlower, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * hupper
  obtain ⟨φ, hφanti, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose x hxupper hxlower hxsmall using fun n => small (φ n) (hφpos n)
  have hS : Tendsto (fun n => (T - μ • 1) (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (by grind) hφ
  have hfact : ∀ v : X, (T ^ 2) v - (μ ^ 2) • v =
      T ((T - μ • 1) v) + μ • ((T - μ • 1) v) := by
    intro v
    simp only [pow_two, mul_apply_eq_comp,
      sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, smul_sub, smul_smul]
    abel
  have herror : Tendsto (fun n => (T ^ 2) (x n) - (μ ^ 2) • x n) atTop (𝓝 0) := by
    simp_rw [hfact]
    simpa using (T.continuous.continuousAt.tendsto.comp hS).add (hS.const_smul μ)
  obtain ⟨K, hK, hKi⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKi ⟨x n, by simpa using hxupper n, rfl⟩)
  have hxlim : Tendsto (fun n => x (ψ n)) atTop (𝓝 ((μ ^ 2)⁻¹ • y)) := by
    have hh := hψy.sub (herror.comp hψ.tendsto_atTop)
    have hh' := hh.const_smul ((μ ^ 2)⁻¹)
    simp only [sub_zero] at hh'
    convert hh' using 1
    ext n
    change x (ψ n) = (μ ^ 2)⁻¹ • ((T ^ 2) (x (ψ n)) -
      ((T ^ 2) (x (ψ n)) - (μ ^ 2) • x (ψ n)))
    rw [sub_sub_cancel, inv_smul_smul₀ (pow_ne_zero 2 hμ)]
  have he : (T - μ • 1) ((μ ^ 2)⁻¹ • y) = 0 :=
    tendsto_nhds_unique ((T - μ • 1).continuous.continuousAt.tendsto.comp hxlim)
      (hS.comp hψ.tendsto_atTop)
  have hz : (μ ^ 2)⁻¹ • y = (0 : X) := hinj (by simpa using he)
  have hn := ge_of_tendsto hxlim.norm (Filter.Eventually.of_forall (fun n => hxlower (ψ n)))
  rw [hz, norm_zero] at hn
  exact (inv_pos.mpr ((zero_lt_one.trans hC))).not_ge hn

/-- Fredholm alternative for compact squares: injectivity of a nonzero shift
already implies surjectivity. -/
theorem surjective_shift [CompleteSpace X] (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    {μ : 𝕜} (hμ : μ ≠ 0)
    (hinj : Function.Injective (T - μ • 1 : X →L[𝕜] X)) :
    Function.Surjective (T - μ • 1 : X →L[𝕜] X) := by
  by_contra hsurj
  let S := T - μ • 1
  obtain ⟨Kbound, hbound⟩ := antilipschitz_shift T hT hμ hinj
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, _, hupper, hmem, hfar⟩ := IsCompactOperator.exists_seq hsurj
    (hbound.isClosedEmbedding S.uniformContinuous) hc (R := ‖c‖ + 1) (by simp)
  have mem {n m : ℕ} (hm : m ≤ n) : f n ∈ ((S : Module.End 𝕜 X) ^ m).range :=
    (S : Module.End 𝕜 X).iterateRange.monotone hm (hmem n)
  have memS {n m : ℕ} (hm : m ≤ n) : S (f n) ∈
      ((S : Module.End 𝕜 X) ^ (m + 1)).range := by
    rw [Module.End.iterate_succ', LinearMap.range_comp]
    exact ⟨f n, mem hm, rfl⟩
  have memSS {n m : ℕ} (hm : m ≤ n) : S (S (f n)) ∈
      ((S : Module.End 𝕜 X) ^ (m + 1)).range := by
    rw [Module.End.iterate_succ', LinearMap.range_comp]
    exact ⟨S (f n), (S : Module.End 𝕜 X).iterateRange.monotone (Nat.le_succ m)
      (memS hm), rfl⟩
  let d (v : X) := S (S v) + (μ + μ) • S v
  have dmem {n m : ℕ} (hm : m ≤ n) : d (f n) ∈
      ((S : Module.End 𝕜 X) ^ (m + 1)).range :=
    Submodule.add_mem _ (memSS hm) (Submodule.smul_mem _ _ (memS hm))
  have factor (v : X) : (T ^ 2) v = d v + (μ ^ 2) • v := by
    simp only [d, S, pow_two, mul_apply_eq_comp,
      sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, smul_sub,
      add_smul, smul_smul]
    module
  have separated : Pairwise fun m n => ‖μ ^ 2‖ ≤ ‖(T ^ 2) (f m) - (T ^ 2) (f n)‖ := by
    have : Std.Symm (fun m n => ‖μ ^ 2‖ ≤ ‖(T ^ 2) (f m) - (T ^ 2) (f n)‖) := by
      constructor
      intro m n h
      simpa only [norm_sub_rev] using h
    apply Pairwise.of_lt
    intro m n hmn
    let u := (μ ^ 2)⁻¹ • (d (f n) - d (f m) + (μ ^ 2) • f n)
    have hu : (μ ^ 2) • (f m - u) = (T ^ 2) (f m) - (T ^ 2) (f n) := by
      rw [smul_sub, smul_inv_smul₀ (pow_ne_zero 2 hμ), factor, factor]
      abel
    have umem : u ∈ ((S : Module.End 𝕜 X) ^ (m + 1)).range :=
      Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.sub_mem _ (dmem hmn.le) (dmem le_rfl))
        (Submodule.smul_mem _ _ (mem hmn)))
    grw [← hu, norm_smul, mul_comm, ← hfar m u umem, one_mul]
  obtain ⟨K, hK, hKi⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKi ⟨f n, by simpa using hupper n, rfl⟩)
  have hcauchy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ‖μ ^ 2‖ (norm_pos_iff.mpr (pow_ne_zero 2 hμ))
  have hclose : ‖(T ^ 2) (f (ψ (N + 1))) - (T ^ 2) (f (ψ N))‖ < ‖μ ^ 2‖ := by
    have hh := hN (N + 1) (Nat.le_succ N)
    change dist ((T ^ 2) (f (ψ (N + 1)))) ((T ^ 2) (f (ψ N))) < ‖μ ^ 2‖ at hh
    simpa only [dist_eq_norm_sub] using hh
  exact hclose.not_ge (separated (by simp [hψ.injective.eq_iff]))

/-- Every nonzero spectral value of a square-compact operator is an eigenvalue. -/
theorem eigenvector_of_mem_spectrum [CompleteSpace X] (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    {μ : 𝕜} (hμ : μ ≠ 0) (hspec : μ ∈ spectrum 𝕜 T) :
    ∃ x : X, x ≠ 0 ∧ T x = μ • x := by
  by_contra! h
  have hinj : Function.Injective (T - μ • 1 : X →L[𝕜] X) := by
    intro x y he
    have hz : (T - μ • 1) (x - y) = 0 := by
      rw [map_sub, he, sub_self]
    have heig : T (x - y) = μ • (x - y) := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hz
    exact sub_eq_zero.mp (by_contra (fun hn => h (x - y) hn heig))
  have hsurj := surjective_shift T hT hμ hinj
  have hunit : IsUnit (T - μ • 1 : X →L[𝕜] X) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩
  have hres : μ ∈ resolventSet 𝕜 T := by
    rw [spectrum.mem_resolventSet_iff]
    simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using hunit.neg
  exact hspec hres

end LeanShared.SquareCompactFredholm
