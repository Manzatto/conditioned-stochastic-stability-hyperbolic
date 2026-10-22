module
public import LeanShared.Analysis.SmoothNonstationarySymbol
public import LeanShared.Analysis.SmoothPartialDerivativeBounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Every actual frequency derivative of the smooth reciprocal-gradient
symbol is uniformly bounded and Holder in a physical matrix field.
Constants are constructed on compact finite-dimensional matrix/frequency
sets; no symbol derivative or Holder estimate is assumed. -/
public noncomputable section
open Set Metric
namespace LeanShared.NonstationarySymbolHolderBounds
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem compact_bounds {δ D Z:ℝ} (positive:0<δ) (hD:0≤D) (hZ:0≤Z)
    (v:E) (n:ℕ):
    ∃B L:ℝ,0≤B ∧ 0≤L ∧
      (∀A:E→L[ℝ]E,‖A‖≤D→∀z:E × E,‖z‖≤Z→
        ‖SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A,z)‖≤B) ∧
      ∀A A':E→L[ℝ]E,‖A‖≤D→‖A'‖≤D→∀z:E × E,‖z‖≤Z→
        ‖SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A,z)-
          SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A',z)‖≤L*‖A-A'‖:=by
  let K:Set ((E→L[ℝ]E) × (E × E)):=closedBall 0 (D+Z)
  have member (A:E→L[ℝ]E) (z:E × E) (hA:‖A‖≤D) (hz:‖z‖≤Z):(A,z)∈K:=by
    change dist (A,z) 0≤D+Z
    rw [dist_zero_right,Prod.norm_def]
    exact max_le (hA.trans (le_add_of_nonneg_right hZ))
      (hz.trans (le_add_of_nonneg_left hD))
  obtain ⟨B,L,hB,hL,value,lip⟩:=SmoothPartialDerivativeBounds.compact_bounds n
    (SmoothNonstationarySymbol.coefficient positive v) (SmoothNonstationarySymbol.smooth positive v)
    (isCompact_closedBall 0 (D+Z)) (convex_closedBall 0 (D+Z))
  refine ⟨B,L,hB,hL,(fun A hA z hz=>value (A,z) (member A z hA hz)),?_⟩
  intro A A' hA hA' z hz
  simpa only [Prod.sub_def,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using
    lip (A,z) (member A z hA hz) (A',z) (member A' z hA' hz)

theorem field_bounds {X P:Type*} [PseudoMetricSpace X]
    {δ D Z H a:ℝ} (positive:0<δ) (hD:0≤D) (hZ:0≤Z)
    (v:E) (n:ℕ) (A:P→X→E→L[ℝ]E) (value:∀p x,‖A p x‖≤D)
    (holder:∀p x y,‖A p x-A p y‖≤H*dist x y^a):
    ∃B L:ℝ,0≤B ∧ 0≤L ∧
      (∀p x (z:E × E),‖z‖≤Z→
        ‖SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A p x,z)‖≤B) ∧
      ∀p x y (z:E × E),‖z‖≤Z→
        ‖SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A p x,z)-
          SmoothPartialDerivativeBounds.frequencyDerivative n
          (SmoothNonstationarySymbol.coefficient positive v) (A p y,z)‖≤L*H*dist x y^a:=by
  obtain ⟨B,L,hB,hL,bound,lip⟩:=compact_bounds positive hD hZ v n
  refine ⟨B,L,hB,hL,(fun p x z hz=>bound _ (value p x) z hz),?_⟩
  intro p x y z hz
  exact (lip _ _ (value p x) (value p y) z hz).trans
    ((mul_le_mul_of_nonneg_left (holder p x y) hL).trans_eq (mul_assoc _ _ _).symm)
end LeanShared.NonstationarySymbolHolderBounds
