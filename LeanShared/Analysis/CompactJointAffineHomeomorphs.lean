module
public import LeanShared.Analysis.CompactParameterDerivativeMargin
public import LeanShared.Analysis.JointSmallAffineHomeomorphs

/-! Actual strict derivative control on a compact legal parameter set
constructs genuine global maps and jointly C1 inverse maps on one OPEN
parameter neighborhood. The compact affine exterior is retained literally. -/
public noncomputable section
open Set
open scoped Topology ContDiff NNReal
namespace LeanShared.CompactJointAffineHomeomorphs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_family (K : Set P) (compactK : IsCompact K)
    (A : E ≃L[ℝ] E) (b : E) (f : P × E → E) (S : Set E) (compactS : IsCompact S)
    (O₀ : Set P) (openO₀ : IsOpen O₀) (contains : K ⊆ O₀)
    (joint : ContDiffOn ℝ 1 f (O₀ ×ˢ univ))
    (exterior : ∀ p ∈ O₀, ∀ x, x ∉ S → f (p,x) = A x+b)
    (k : ℝ≥0) (positive : 0 < k)
    (small : Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (margin : ∀ p ∈ K, ∀ x, ‖fderiv ℝ (fun z => f (p,z)) x-A.toContinuousLinearMap‖ < k) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ O ⊆ O₀ ∧ ∃ H : P → E ≃ₜ E,
      (∀ p ∈ O, ∀ x, H p x = f (p,x)) ∧
      ContDiffOn ℝ 1 (fun q : P × E => H q.1 q.2) (O ×ˢ univ) ∧
      ContDiffOn ℝ 1 (fun q : P × E => (H q.1).symm q.2) (O ×ˢ univ) := by
  obtain ⟨O,openO,containsK,subset,close⟩ := CompactParameterDerivativeMargin.exists_window K compactK
    A.toContinuousLinearMap b f S compactS O₀ openO₀ contains joint exterior k (by exact_mod_cast positive) margin
  have regular : ContDiffOn ℝ 1 f (O ×ˢ univ) := joint.mono (fun q hq => ⟨subset hq.1,hq.2⟩)
  obtain ⟨H,actual,forward,inverse⟩ := JointSmallAffineHomeomorphs.exists_family A b f O openO regular k small
    (fun p hp x => (close p hp x).le)
  exact ⟨O,openO,containsK,subset,H,actual,forward,inverse⟩

end LeanShared.CompactJointAffineHomeomorphs
