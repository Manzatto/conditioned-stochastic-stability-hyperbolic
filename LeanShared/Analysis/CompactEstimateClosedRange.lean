module

public import LeanShared.Analysis.CompactTwoNormEigenSpace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Tactic.LinearCombination

/-! Peetre's compact estimate implies finite kernel and closed range, for
operators between different Banach/normed spaces. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.CompactEstimateClosedRange
variable {E Y W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Peetre's compactness argument for an injective operator. -/
theorem antilipschitz_of_compact_estimate (S : E →L[ℂ] Y) (i : E →L[ℂ] W)
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
  have small : ∀ ε > 0, ∃ x : E, ‖x‖ ≤ 1 ∧ (2 : ℝ)⁻¹ ≤ ‖x‖ ∧ ‖S x‖ < ε := by
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


/-- A compact estimate forces the kernel to be finite dimensional. -/
theorem finite_kernel (S : E →L[ℂ] Y) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (A B : ℝ) (hB : 0 ≤ B)
    (estimate : ∀ x, ‖x‖ ≤ A * ‖S x‖ + B * ‖i x‖) :
    FiniteDimensional ℂ S.ker := by
  let K := S.ker
  let : CompleteSpace K := S.isClosed_ker.isComplete.completeSpace_coe
  let j : K →L[ℂ] W := i.comp K.subtypeL
  have hj : IsCompactOperator j := hi.comp_clm K.subtypeL
  apply CompactTwoNormEigenSpace.finiteDimensional_of_compact_bound j hj B hB
  intro x
  change ‖x.val‖ ≤ B * ‖i x.val‖
  have hz : S x.val = 0 := x.property
  simpa only [hz, norm_zero, mul_zero, zero_add] using estimate x.val

/-- Peetre's compact estimate gives closed range; finite-dimensional kernel
complementation is proved by Hahn–Banach and is not a source premise. -/
theorem closed_range (S : E →L[ℂ] Y) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (estimate : ∀ x, ‖x‖ ≤ A * ‖S x‖ + B * ‖i x‖) :
    IsClosed (S.range : Set Y) := by
  let K := S.ker
  let _ : FiniteDimensional ℂ K := finite_kernel S i hi A B hB estimate
  obtain ⟨V, hVclosed, hcompl⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional K).exists_isClosed_isCompl
  let : CompleteSpace V := hVclosed.isComplete.completeSpace_coe
  let Sj : V →L[ℂ] Y := S.comp V.subtypeL
  let ij : V →L[ℂ] W := i.comp V.subtypeL
  have hij : IsCompactOperator ij := hi.comp_clm V.subtypeL
  have hinj : Function.Injective Sj := by
    intro x y he
    change S x.val = S y.val at he
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hk : x.val - y.val ∈ K := by
      change S (x.val - y.val) = 0
      rw [map_sub, he, sub_self]
    have hv : x.val - y.val ∈ V := V.sub_mem x.property y.property
    exact hcompl.disjoint.le_bot ⟨hk, hv⟩
  have est : ∀ x : V, ‖x‖ ≤ A * ‖Sj x‖ + B * ‖ij x‖ := fun x => estimate x.val
  obtain ⟨Kanti, hanti⟩ := antilipschitz_of_compact_estimate Sj ij hij hinj A B hA hB est
  have rangeEqual : Set.range S = Set.range Sj := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      have hxmem : x ∈ K ⊔ V := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨k, hk, v, hv, hkv⟩ := Submodule.mem_sup.mp hxmem
      refine ⟨⟨v, hv⟩, ?_⟩
      change S v = y
      rw [← hx, ← hkv, map_add]
      have hSk : S k = 0 := hk
      simp only [hSk, zero_add]
    · rintro ⟨v, hv⟩
      exact ⟨v.val, hv⟩
  change IsClosed (Set.range S)
  rw [rangeEqual]
  exact hanti.isClosed_range Sj.uniformContinuous

end LeanShared.CompactEstimateClosedRange
