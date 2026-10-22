module

public import LeanShared.Analysis.StableRangeInverse
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Finite stable kernel/range splitting excludes all nearby nonzero spectral
shifts by actual invertibility of the stable-range block. -/

public section
set_option maxHeartbeats 800000
open ContinuousLinearMap Submodule Filter Topology
namespace LeanShared.StableRangeSpectralIsolation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Bounded invertibility gives a genuine resolvent neighbourhood at zero. -/
theorem exists_small_shift_bijective (e : E ≃L[ℂ] E) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℂ, ‖u‖ < r →
      Function.Bijective (u • (1 : E →L[ℂ] E) - e.toContinuousLinearMap) := by
  have hunit : IsUnit e.toContinuousLinearMap :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective
  have hzero : (0 : ℂ) ∈ resolventSet ℂ e.toContinuousLinearMap := by
    simpa only [spectrum.mem_resolventSet_iff, ← spectrum.notMem_iff,
      spectrum.zero_notMem_iff] using hunit
  have hnhds := (spectrum.isOpen_resolventSet e.toContinuousLinearMap).mem_nhds hzero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r, hr, fun u hu => ?_⟩
  have huunit : IsUnit (u • (1 : E →L[ℂ] E) - e.toContinuousLinearMap) :=
    hball (show u ∈ Metric.ball (0 : ℂ) r by simpa using hu)
  exact ContinuousLinearMap.isUnit_iff_bijective.mp huunit

/-- A stable complementary range excludes nearby nonzero eigenvalues. -/
theorem exists_punctured_injective (S : E →L[ℂ] E) (n : ℕ)
    (hcompl : IsTopCompl (S ^ n).ker (S ^ n).range)
    (hker : (S ^ (n + 1)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + 1)).range = (S ^ n).range) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℂ, ‖u‖ < r → u ≠ 0 →
      Function.Injective (S - u • 1 : E →L[ℂ] E) := by
  let V := (S ^ n).range
  let : CompleteSpace V := hcompl.isClosed'.isComplete.completeSpace_coe
  obtain ⟨e, he⟩ := StableRangeInverse.exists_equiv S n hcompl hker hrange
  obtain ⟨r, hr, hbij⟩ := exists_small_shift_bijective e
  refine ⟨r, hr, fun u hu hu0 => ?_⟩
  have huinj := (hbij u hu).1
  have zeroOnly : ∀ x : E, (S - u • 1) x = 0 → x = 0 := by
    intro x hx
    have eigen : S x = u • x := by simpa only [sub_apply, smul_apply, one_apply_eq_self,
      sub_eq_zero] using hx
    have powers (k : ℕ) : (S ^ k) x = u ^ k • x := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, eigen, smul_smul, pow_succ]
    have hmem : u ^ n • x ∈ V := by rw [← powers n]; exact ⟨x, rfl⟩
    have xmem : x ∈ V := by
      have hh := V.smul_mem ((u ^ n)⁻¹) hmem
      simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero n hu0), one_smul] using hh
    let xv : V := ⟨x, xmem⟩
    have hz : (u • (1 : V →L[ℂ] V) - e.toContinuousLinearMap) xv = 0 := by
      apply Subtype.ext
      change u • x - (e xv).val = 0
      rw [he, eigen, sub_self]
    have hzv : xv = 0 := huinj (by simpa only [map_zero] using hz)
    exact congrArg Subtype.val hzv
  intro x y hxy
  have hz := zeroOnly (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hz

end LeanShared.StableRangeSpectralIsolation
