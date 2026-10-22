module
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Quantitative phase separation in the two radially nonresonant
regions. The loss is fixed by the actual inverse derivative norm,
independently of frequency levels and cone signs. -/
public noncomputable section
namespace LeanShared.RadialPhaseSeparation
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gap (A:E→L[ℝ] E) {B K a b:ℝ} (hB:1≤B) (hK:1≤K)
    (operator:‖A‖≤B) (inverse:∀η,‖η‖≤K*‖A η‖)
    (ha:0<a) (hb:0<b) (ξ η:E)
    (upperξ:‖ξ‖≤2*a) (upperη:‖η‖≤4*b)
    (nonresonant:(a/2≤‖ξ‖ ∧16*B*b≤a) ∨(b/4≤‖η‖ ∧16*K*a≤b)):
    (8*K)⁻¹*max a b≤‖ξ-A η‖:=by
  have hKpos:0<K:=by linarith
  have triangle:‖A η‖≤‖ξ‖+‖ξ-A η‖:=by
    have h:=norm_sub_le ξ (ξ-A η)
    have eq:ξ-(ξ-A η)=A η:=by abel
    rw [eq] at h
    exact h
  have triangle':‖ξ‖≤‖ξ-A η‖+‖A η‖:=by
    have h:=norm_add_le (ξ-A η) (A η)
    simpa only [sub_add_cancel] using h
  rcases nonresonant with ⟨lower,dominant⟩|⟨lower,dominant⟩
  · have ab:b≤a:=by nlinarith
    rw [max_eq_left ab]
    have applied:‖A η‖≤4*B*b:=by
      calc
        ‖A η‖≤‖A‖*‖η‖:=A.le_opNorm η
        _≤B*‖η‖:=mul_le_mul_of_nonneg_right operator (norm_nonneg _)
        _≤B*(4*b):=mul_le_mul_of_nonneg_left upperη (by linarith)
        _=4*B*b:=by ring
    have large:a/4≤‖ξ-A η‖:=by linarith
    have c:(8*K)⁻¹≤1/4:=by
      apply (inv_le_comm₀ (by positivity) (by norm_num : (0:ℝ)<1/4)).2
      norm_num
      linarith
    exact (mul_le_mul_of_nonneg_right c ha.le).trans (by linarith)
  · have ab:a≤b:=by nlinarith
    rw [max_eq_right ab]
    have ηbound:=inverse η
    have combined:b/4≤K*(2*a+‖ξ-A η‖):=by
      calc
        b/4≤‖η‖:=lower
        _≤K*‖A η‖:=ηbound
        _≤K*(2*a+‖ξ-A η‖):=mul_le_mul_of_nonneg_left
          (triangle.trans (add_le_add upperξ le_rfl)) hKpos.le
    apply (inv_mul_le_iff₀ (by positivity : 0<8*K)).2
    nlinarith

theorem gap_of_equiv (A:E≃L[ℝ] E) {B K a b:ℝ} (hB:1≤B) (hK:1≤K)
    (operator:‖(A:E→L[ℝ] E)‖≤B) (inverse:‖(A.symm:E→L[ℝ] E)‖≤K)
    (ha:0<a) (hb:0<b) (ξ η:E)
    (upperξ:‖ξ‖≤2*a) (upperη:‖η‖≤4*b)
    (nonresonant:(a/2≤‖ξ‖ ∧16*B*b≤a) ∨(b/4≤‖η‖ ∧16*K*a≤b)):
    (8*K)⁻¹*max a b≤‖ξ-A η‖:=by
  apply gap (A:E→L[ℝ] E) hB hK operator ?_ ha hb ξ η upperξ upperη nonresonant
  intro z
  calc
    ‖z‖=‖A.symm (A z)‖:=by rw [A.symm_apply_apply]
    _≤‖(A.symm:E→L[ℝ] E)‖*‖A z‖:=A.symm.toContinuousLinearMap.le_opNorm _
    _≤K*‖A z‖:=mul_le_mul_of_nonneg_right inverse (norm_nonneg _)
end LeanShared.RadialPhaseSeparation
