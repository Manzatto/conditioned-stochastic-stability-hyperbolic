module
public import LeanShared.Analysis.CompactLinearFamilyCoercivity
public import LeanShared.Analysis.RadialPhaseSeparation
public import LeanShared.Analysis.DyadicFrequencyScale

/-! The low-frequency branches also have a uniform nonstationary gap
outside a constructed finite level. The required inverse bound is
derived from actual compactness and injectivity. -/
public noncomputable section
namespace LeanShared.NormalizedLowFrequencyPhaseGap
open DyadicFrequencyScale
variable {E X:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [CompactSpace X]

theorem exists_gap (A:X→E→L[ℝ] E) (continuous:Continuous A)
    (injective:∀x,Function.Injective (A x)):
    ∃δ:ℝ,0<δ ∧∃N:ℕ,∀x n l,(n=0 ∨l=0) → N<max n l →
      ∀ξ η:E,‖ξ‖≤2 → ‖η‖≤4 →
      (n≠0 → 1/2≤‖ξ‖) → (l≠0 → 1/4≤‖η‖) →
      δ≤‖leftRatio n l • ξ-A x (rightRatio n l • η)‖^2:=by
  obtain ⟨B,K,hB,hK,operator,inverse⟩:=CompactLinearFamilyCoercivity.bounds A continuous injective
  obtain ⟨N,threshold⟩:=pow_unbounded_of_one_lt (max (16*B) (16*K)) (by norm_num : (1:ℝ)<2)
  let c:ℝ:=(8*K)⁻¹
  have cp:0<c:=inv_pos.mpr (by linarith)
  refine ⟨c^2,sq_pos_of_pos cp,N,?_⟩
  intro x n l low large ξ η ξhi ηhi ξlo ηlo
  have an:0<(2:ℝ)^n:=by positivity
  have al:0<(2:ℝ)^l:=by positivity
  have high:16*B*(2:ℝ)^l≤(2:ℝ)^n ∨16*K*(2:ℝ)^n≤(2:ℝ)^l:=by
    rcases low with hn|hl
    · have nl:N<l:=by simpa only [hn,Nat.zero_max] using large
      have bound:=pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) nl.le
      right
      simpa only [hn,pow_zero,mul_one] using
        (le_max_right (16*B) (16*K)).trans (threshold.le.trans bound)
    · have nn:N<n:=by simpa only [hl,Nat.max_zero] using large
      have bound:=pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) nn.le
      left
      simpa only [hl,pow_zero,mul_one] using
        (le_max_left (16*B) (16*K)).trans (threshold.le.trans bound)
  have ξupper:‖((2:ℝ)^n) • ξ‖≤2*(2:ℝ)^n:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos an]
    nlinarith
  have ηupper:‖((2:ℝ)^l) • η‖≤4*(2:ℝ)^l:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos al]
    nlinarith
  have selection:((2:ℝ)^n/2≤‖((2:ℝ)^n) • ξ‖ ∧16*B*(2:ℝ)^l≤(2:ℝ)^n) ∨
      ((2:ℝ)^l/4≤‖((2:ℝ)^l) • η‖ ∧16*K*(2:ℝ)^n≤(2:ℝ)^l):=by
    rcases high with first|second
    · have hn:n≠0:=by
        intro zero
        have atLeast:1≤(2:ℝ)^l:=one_le_pow₀ (by norm_num)
        simp only [zero,pow_zero] at first
        nlinarith
      left
      refine ⟨?_,first⟩
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos an]
      nlinarith [ξlo hn]
    · have hl:l≠0:=by
        intro zero
        have atLeast:1≤(2:ℝ)^n:=one_le_pow₀ (by norm_num)
        simp only [zero,pow_zero] at second
        nlinarith
      right
      refine ⟨?_,second⟩
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos al]
      nlinarith [ηlo hl]
  have bound:=RadialPhaseSeparation.gap (A x) hB hK (operator x) (inverse x) an al
    (((2:ℝ)^n) • ξ) (((2:ℝ)^l) • η) ξupper ηupper selection
  have eq:max ((2:ℝ)^n) ((2:ℝ)^l)=major n l:=by
    rcases le_total n l with h|h
    · simp only [major,max_eq_right h,max_eq_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) h)]
    · simp only [major,max_eq_left h,max_eq_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) h)]
  have factor:((2:ℝ)^n) • ξ-A x (((2:ℝ)^l) • η)=
      major n l • (leftRatio n l • ξ-A x (rightRatio n l • η)):=by
    rw [smul_sub,smul_smul,←map_smul,smul_smul,left_identity,right_identity]
  rw [eq,factor,norm_smul,Real.norm_eq_abs,abs_of_pos (positive n l)] at bound
  have normalized:c≤‖leftRatio n l • ξ-A x (rightRatio n l • η)‖:=
    (mul_le_mul_iff_right₀ (positive n l)).mp (by simpa only [c,mul_comm] using bound)
  nlinarith [norm_nonneg (leftRatio n l • ξ-A x (rightRatio n l • η))]
end LeanShared.NormalizedLowFrequencyPhaseGap
