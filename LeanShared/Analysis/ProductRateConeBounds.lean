module
public import LeanShared.Analysis.ProductBlockPreimageCone
import Mathlib.Tactic

/-! One small matrix budget at any original rate in (0,1) preserves a
fixed narrow aperture and gives contracting stable/inverse-unstable norm
bounds. No strong-iterate rate or word-dependent constant is required. -/
public noncomputable section
open Set
namespace LeanShared.ProductRateConeBounds
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem unstable_component (U : X ≃L[ℝ] X) (S : Y →L[ℝ] Y)
    (B : (X×Y) →L[ℝ] (X×Y)) {q δ : ℝ} (positiveQ : 0 < q)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ q)
    (close : ‖B-U.toContinuousLinearMap.prodMap S‖ ≤ δ)
    (z : X×Y) (input : ‖z.2‖ ≤ ‖z.1‖) :
    (1/q-δ)*‖z‖ ≤ ‖(B z).1‖ := by
  have nz : ‖z‖ = ‖z.1‖ := by rw [Prod.norm_def, max_eq_left input]
  have error := (norm_fst_le ((B-U.toContinuousLinearMap.prodMap S) z)).trans
    (((B-U.toContinuousLinearMap.prodMap S).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right close (norm_nonneg z)))
  change ‖(B z).1-U z.1‖ ≤ δ*‖z‖ at error
  have undo := U.symm.toContinuousLinearMap.le_opNorm (U z.1)
  change ‖U.symm (U z.1)‖ ≤ _ at undo
  rw [U.symm_apply_apply] at undo
  have lower : (1/q)*‖z.1‖ ≤ ‖U z.1‖ := by
    have divide : ‖z.1‖/q ≤ ‖U z.1‖ := (div_le_iff₀ positiveQ).mpr
      (by nlinarith [undo.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg (U z.1)))])
    calc
      (1/q)*‖z.1‖ = ‖z.1‖/q := by ring
      _ ≤ ‖U z.1‖ := divide
  have triangle := norm_sub_norm_le (U z.1) (B z).1
  rw [norm_sub_rev] at triangle
  rw [nz] at error ⊢
  nlinarith

theorem forward_cone (U : X ≃L[ℝ] X) (S : Y →L[ℝ] Y)
    (B : (X×Y) →L[ℝ] (X×Y)) {q δ c : ℝ} (positiveQ : 0 < q)
    (nonnegativeC : 0 ≤ c) (smallC : c ≤ 1)
    (stable : ‖S‖ ≤ q) (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ q)
    (close : ‖B-U.toContinuousLinearMap.prodMap S‖ ≤ δ)
    (separation : q*c+δ ≤ c*(1/q-δ))
    (z : X×Y) (input : ‖z.2‖ ≤ c*‖z.1‖) :
    ‖(B z).2‖ ≤ c*‖(B z).1‖ := by
  have wide : ‖z.2‖ ≤ ‖z.1‖ := input.trans
    (mul_le_of_le_one_left (norm_nonneg _) smallC)
  have nz : ‖z‖ = ‖z.1‖ := by rw [Prod.norm_def, max_eq_left wide]
  have error := (norm_snd_le ((B-U.toContinuousLinearMap.prodMap S) z)).trans
    (((B-U.toContinuousLinearMap.prodMap S).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right close (norm_nonneg z)))
  change ‖(B z).2-S z.2‖ ≤ δ*‖z‖ at error
  have boundS := (S.le_opNorm z.2).trans
    (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have triangle := norm_sub_norm_le (B z).2 (S z.2)
  have lower := unstable_component U S B positiveQ unstable close z wide
  rw [nz] at error lower
  have upper : ‖(B z).2‖ ≤ (q*c+δ)*‖z.1‖ := by
    have scale := mul_le_mul_of_nonneg_left input positiveQ.le
    nlinarith
  exact upper.trans ((mul_le_mul_of_nonneg_right separation (norm_nonneg _)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left lower nonnegativeC))

theorem stable_norm (U : X →L[ℝ] X) (S : Y →L[ℝ] Y)
    (B : (X×Y) →L[ℝ] (X×Y)) {q δ : ℝ} (stable : ‖S‖ ≤ q)
    (close : ‖B-U.prodMap S‖ ≤ δ) (z : X×Y)
    (input : ‖z.1‖ ≤ ‖z.2‖) (output : ‖(B z).1‖ ≤ ‖(B z).2‖) :
    ‖B z‖ ≤ (q+δ)*‖z‖ := by
  have nz : ‖z‖ = ‖z.2‖ := by rw [Prod.norm_def, max_eq_right input]
  have nB : ‖B z‖ = ‖(B z).2‖ := by rw [Prod.norm_def, max_eq_right output]
  have error := (norm_snd_le ((B-U.prodMap S) z)).trans
    (((B-U.prodMap S).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right close (norm_nonneg z)))
  change ‖(B z).2-S z.2‖ ≤ δ*‖z‖ at error
  have boundS := (S.le_opNorm z.2).trans
    (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have triangle := norm_sub_norm_le (B z).2 (S z.2)
  rw [nz] at error ⊢
  rw [nB]
  nlinarith

/-- All scalar inequalities are selected simultaneously before any
diagonal block or actual matrix. The two resulting rates are below one. -/
theorem exists_budget {q c : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (positiveC : 0 < c) (smallC : c ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ q+δ < 1 ∧ 1 < 1/q-δ ∧
      ∀ (U : X ≃L[ℝ] X) (S : Y →L[ℝ] Y) (B : (X×Y) →L[ℝ] (X×Y)),
        ‖S‖ ≤ q → ‖U.symm.toContinuousLinearMap‖ ≤ q →
        ‖B-U.toContinuousLinearMap.prodMap S‖ ≤ δ →
        (∀ z, ‖(B z).1‖ ≤ c*‖(B z).2‖ → ‖z.1‖ ≤ c*‖z.2‖) ∧
        (∀ z, ‖z.2‖ ≤ c*‖z.1‖ → ‖(B z).2‖ ≤ c*‖(B z).1‖) ∧
        (∀ z, ‖(B z).1‖ ≤ ‖(B z).2‖ →
          ‖z.1‖ ≤ ‖z.2‖ ∧ ‖B z‖ ≤ (q+δ)*‖z‖) ∧
        ∀ z, ‖z.2‖ ≤ ‖z.1‖ →
          ‖(B z).2‖ ≤ ‖(B z).1‖ ∧ ‖z‖ ≤ (1/q-δ)⁻¹*‖B z‖ := by
  have inverseGreater : 1 < 1/q := (lt_div_iff₀ positiveQ).mpr (by linarith)
  have gap : q < 1/q := contractingQ.trans inverseGreater
  let V : Set ℝ := {t | 0 < 1/q-t-c*t ∧
    t+c*(q+t) < c*(1/q-t-c*t) ∧
    0 < 1/q-t-t ∧ t+(q+t) < 1/q-t-t ∧ q+t < 1 ∧ 1 < 1/q-t}
  have openFirst : IsOpen {t : ℝ | 0 < 1/q-t-c*t} := isOpen_lt continuous_const (by fun_prop)
  have openSecond : IsOpen {t : ℝ | t+c*(q+t) < c*(1/q-t-c*t)} := isOpen_lt (by fun_prop) (by fun_prop)
  have openThird : IsOpen {t : ℝ | 0 < 1/q-t-t} := isOpen_lt continuous_const (by fun_prop)
  have openFourth : IsOpen {t : ℝ | t+(q+t) < 1/q-t-t} := isOpen_lt (by fun_prop) (by fun_prop)
  have openFifth : IsOpen {t : ℝ | q+t < 1} := isOpen_lt (by fun_prop) continuous_const
  have openSixth : IsOpen {t : ℝ | 1 < 1/q-t} := isOpen_lt continuous_const (by fun_prop)
  have openV : IsOpen V := openFirst.inter (openSecond.inter
    (openThird.inter (openFourth.inter (openFifth.inter openSixth))))
  have zeroV : (0 : ℝ) ∈ V := by
    change 0 < 1/q-0-c*0 ∧ 0+c*(q+0) < c*(1/q-0-c*0) ∧
      0 < 1/q-0-0 ∧ 0+(q+0) < 1/q-0-0 ∧ q+0 < 1 ∧ 1 < 1/q-0
    simpa only [sub_zero, mul_zero, zero_add, add_zero] using
      And.intro (by linarith : 0 < 1/q)
        (And.intro (mul_lt_mul_of_pos_left gap positiveC)
          (And.intro (by linarith : 0 < 1/q) (And.intro gap (And.intro contractingQ inverseGreater))))
  obtain ⟨R, positiveR, ball⟩ := Metric.mem_nhds_iff.mp (openV.mem_nhds zeroV)
  let δ : ℝ := R/2
  have positiveδ : 0 < δ := half_pos positiveR
  have conditions : δ ∈ V := by
    apply ball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos positiveδ]
    exact half_lt_self positiveR
  obtain ⟨positiveNarrow, narrow, positiveWide, wide, contracting, expanding⟩ := conditions
  have narrowForward : q*c+δ ≤ c*(1/q-δ) := by
    calc
      _ ≤ δ+c*(q+δ) := by nlinarith [mul_nonneg positiveC.le positiveδ.le]
      _ ≤ c*(1/q-δ-c*δ) := narrow.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg positiveC.le positiveδ.le)) positiveC.le
  have wideForward : q*1+δ ≤ 1*(1/q-δ) := by nlinarith
  refine ⟨δ, positiveδ, contracting, expanding, fun U S B stable unstable close => ?_⟩
  have backwardNarrow := ProductBlockPreimageCone.bound U S B positiveQ positiveδ.le positiveC.le
    stable unstable close positiveNarrow narrow.le
  have backwardWide := ProductBlockPreimageCone.bound U S B (κ := 1) (κ' := 1) positiveQ positiveδ.le (by norm_num : (0:ℝ) ≤ 1)
    stable unstable close (by simpa only [one_mul] using positiveWide)
      (by simpa only [one_mul] using wide.le)
  refine ⟨backwardNarrow, forward_cone U S B positiveQ positiveC.le smallC stable unstable close narrowForward, ?_, ?_⟩
  · intro z target
    have input : ‖z.1‖ ≤ ‖z.2‖ := by simpa only [one_mul] using backwardWide z (by simpa only [one_mul] using target)
    exact ⟨input, stable_norm U.toContinuousLinearMap S B stable close z input target⟩
  · intro z input
    have output : ‖(B z).2‖ ≤ ‖(B z).1‖ := by
      simpa only [one_mul] using forward_cone U S B positiveQ (by norm_num : (0:ℝ) ≤ 1)
        le_rfl stable unstable close wideForward z (by simpa only [one_mul] using input)
    have lower := (unstable_component U S B positiveQ unstable close z input).trans (norm_fst_le (B z))
    have divide : ‖z‖ ≤ ‖B z‖/(1/q-δ) := (le_div_iff₀ (by linarith : 0 < 1/q-δ)).mpr (by nlinarith)
    exact ⟨output, by simpa only [div_eq_mul_inv, mul_comm] using divide⟩

end LeanShared.ProductRateConeBounds
