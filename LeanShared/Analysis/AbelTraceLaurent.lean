module
public import LeanShared.Analysis.StableRangeInverse
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Finite Laurent expansion of the resolvent at a stable Fitting point. If
`S = B - c` has a topological Fitting splitting `E = ker S^n ⊕ range S^n` with
stable kernels and ranges, and `P` is the projection onto the kernel, then near `c`
the resolvent equals `∑_{j ≤ n} (w - c)^{-(j+1)} S^j P` up to a uniformly bounded
operator. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Finset ContinuousLinearMap Submodule
namespace LeanShared.AbelTraceLaurent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem laurent (B : E →L[ℂ] E) (c : ℂ) (n : ℕ)
    (compl : IsTopCompl ((B - c • 1) ^ n).ker ((B - c • 1) ^ n).range)
    (hker : ((B - c • 1) ^ (n + 1)).ker = ((B - c • 1) ^ n).ker)
    (hrange : ((B - c • 1) ^ (n + 1)).range = ((B - c • 1) ^ n).range) :
    ∃ M ρ : ℝ, 0 < ρ ∧ ∀ w ∈ resolventSet ℂ B, ‖w - c‖ < ρ → w ≠ c →
      ‖resolvent B w - ∑ j ∈ range (n + 1), ((w - c)⁻¹) ^ (j + 1) •
        ((B - c • 1) ^ j *
          ((B - c • 1) ^ n).ker.projectionL ((B - c • 1) ^ n).range compl)‖ ≤ M := by
  set S := B - c • (1 : E →L[ℂ] E) with hS
  set K := (S ^ n).ker
  set V := (S ^ n).range
  set P := K.projectionL V compl with hP
  set Pc := V.projectionL K compl.symm with hPc
  let : CompleteSpace V := compl.isClosed'.isComplete.completeSpace_coe
  obtain ⟨e, he⟩ := StableRangeInverse.exists_equiv S n compl hker hrange
  let G : E →L[ℂ] E :=
    V.subtypeL ∘L (e.symm.toContinuousLinearMap ∘L V.projectionOntoL K compl.symm)
  have SG : S * G = Pc := by
    ext x
    change S ((e.symm (V.projectionOntoL K compl.symm x) : V) : E) = Pc x
    rw [← he, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have PG : P * G = 0 := by
    ext x
    exact Submodule.projectionL_apply_right compl ⟨_, (e.symm _).property⟩
  have complement : Pc = 1 - P := Submodule.projectionL_eq_id_sub_projectionL compl
  have PcG : Pc * G = G := by rw [complement, sub_mul, one_mul, PG, sub_zero]
  have SnP : S ^ n * P = 0 := by
    ext x
    exact Submodule.projectionL_apply_mem compl x
  have SnP' : S ^ (n + 1) * P = 0 := by rw [pow_succ', mul_assoc, SnP, mul_zero]
  set M : ℝ := 2 * ‖G‖
  refine ⟨M, 1 / (2 * (‖G‖ + 1)), by positivity, fun w hw close hne => ?_⟩
  set y := (w - c)⁻¹ with hy
  have hwc : w - c ≠ 0 := sub_ne_zero.mpr hne
  have unit : IsUnit (algebraMap ℂ (E →L[ℂ] E) w - B) := spectrum.mem_resolventSet_iff.mp hw
  set R := resolvent B w with hR
  have left : R * (algebraMap ℂ (E →L[ℂ] E) w - B) = 1 := by
    rw [hR, spectrum.resolvent_eq hw]; exact unit.val_inv_mul
  have shift : algebraMap ℂ (E →L[ℂ] E) w - B = (w - c) • 1 - S := by
    rw [hS, Algebra.algebraMap_eq_smul_one, sub_smul]; abel
  set L := ∑ j ∈ range (n + 1), y ^ (j + 1) • (S ^ j * P) with hL
  have inverseL : (algebraMap ℂ (E →L[ℂ] E) w - B) * L = P := by
    let f : ℕ → E →L[ℂ] E := fun j => y ^ j • (S ^ j * P)
    have step (j : ℕ) : ((w - c) • 1 - S) * (y ^ (j + 1) • (S ^ j * P)) = f j - f (j + 1) := by
      have scalar : (w - c) * y ^ (j + 1) = y ^ j := by
        rw [pow_succ', ← mul_assoc, hy, mul_inv_cancel₀ hwc, one_mul]
      simp only [f, sub_mul, smul_mul_assoc, one_mul, mul_smul_comm, ← mul_assoc, ← pow_succ']
      rw [smul_sub, smul_smul, mul_comm (y ^ (j + 1)), scalar]
    rw [shift, hL, Finset.mul_sum, Finset.sum_congr rfl fun j _ => step j,
      Finset.sum_range_sub']
    simp only [f, SnP', pow_zero, one_smul, one_mul, smul_zero, sub_zero]
  have RP : R * P = L := by rw [← inverseL, ← mul_assoc, left, one_mul]
  set Z := R * Pc with hZ
  have split : R - L = Z := by
    rw [← RP, hZ, complement, mul_sub, mul_one]
  have identity : Z = (w - c) • (Z * G) - G := by
    have RG : R * G = Z * G := by rw [hZ, mul_assoc, PcG]
    calc Z = R * (S * G) := by rw [SG]
      _ = R * (((w - c) • 1 - (algebraMap ℂ (E →L[ℂ] E) w - B)) * G) := by
          rw [shift, sub_sub_cancel]
      _ = (w - c) • (R * G) - (R * (algebraMap ℂ (E →L[ℂ] E) w - B)) * G := by
          rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc]
      _ = (w - c) • (Z * G) - G := by rw [RG, left, one_mul]
  have small : ‖w - c‖ * ‖G‖ ≤ 1 / 2 := by
    have hG : 0 ≤ ‖G‖ := norm_nonneg _
    have key : ‖w - c‖ * (2 * (‖G‖ + 1)) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (‖G‖ + 1))).mp close
      linarith
    nlinarith [norm_nonneg (w - c)]
  have bound : ‖Z‖ ≤ ‖w - c‖ * ‖G‖ * ‖Z‖ + ‖G‖ := by
    calc ‖Z‖ = ‖(w - c) • (Z * G) - G‖ := by rw [← identity]
      _ ≤ ‖(w - c) • (Z * G)‖ + ‖G‖ := norm_sub_le _ _
      _ ≤ ‖w - c‖ * (‖Z‖ * ‖G‖) + ‖G‖ := by
          rw [norm_smul]
          exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)) le_rfl
      _ = ‖w - c‖ * ‖G‖ * ‖Z‖ + ‖G‖ := by ring
  rw [split]
  nlinarith [norm_nonneg Z, mul_le_mul_of_nonneg_right small (norm_nonneg Z)]

end LeanShared.AbelTraceLaurent
