module
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! Finite pseudo-orbits concatenate through an actual finite bridge without
increasing their one-step error. The construction preserves both words
exactly, including both seams. -/
public noncomputable section
namespace LeanShared.FinitePseudoOrbitConcatenation
variable {X:Type*} [MetricSpace X] {m n g:ℕ}
  (a:Fin (m+1)→X) (b:Fin (n+1)→X) (bridge:Fin (g+1)→X)

@[expose] def word (j:Fin (m+g+n+1)) : X :=
  if hleft:j.val≤m then a ⟨j.val,by omega⟩
  else if hright:m+g≤j.val then b ⟨j.val-m-g,by omega⟩
  else bridge ⟨j.val-m,by omega⟩

omit [MetricSpace X] in
theorem left_index (j:Fin (m+g+n+1)) (hj:j.val≤m) :
    word a b bridge j=a ⟨j.val,by omega⟩ := by
  simp only [word]
  split_ifs
  rfl

omit [MetricSpace X] in
theorem right_index (positive:0<g) (j:Fin (m+g+n+1)) (hj:m+g≤j.val) :
    word a b bridge j=b ⟨j.val-m-g,by omega⟩ := by
  simp only [word]
  split_ifs with hleft
  · omega
  · rfl

omit [MetricSpace X] in
theorem middle_index (positive:0<g)
    (first:bridge ⟨0,by omega⟩=a ⟨m,by omega⟩)
    (last:bridge ⟨g,by omega⟩=b ⟨0,by omega⟩)
    (j:Fin (m+g+n+1)) (lower:m≤j.val) (upper:j.val≤m+g) :
    word a b bridge j=bridge ⟨j.val-m,by omega⟩ := by
  by_cases hleft:j.val≤m
  · have ix:j.val=m := by omega
    have value := left_index a b bridge j hleft
    have leftPoint : (⟨j.val,by omega⟩:Fin (m+1))=⟨m,by omega⟩ := Fin.ext ix
    have bridgePoint : (⟨j.val-m,by omega⟩:Fin (g+1))=⟨0,by omega⟩ := Fin.ext (show j.val-m=0 by omega)
    exact value.trans ((congrArg a leftPoint).trans (first.symm.trans (congrArg bridge bridgePoint).symm))
  by_cases hright:m+g≤j.val
  · have value := right_index a b bridge positive j hright
    have rightPoint : (⟨j.val-m-g,by omega⟩:Fin (n+1))=⟨0,by omega⟩ := Fin.ext (show j.val-m-g=0 by omega)
    have bridgePoint : (⟨j.val-m,by omega⟩:Fin (g+1))=⟨g,by omega⟩ := Fin.ext (show j.val-m=g by omega)
    exact value.trans ((congrArg b rightPoint).trans (last.symm.trans (congrArg bridge bridgePoint).symm))
  · simp [word,hleft,hright]

theorem step_bound (T:X→X) (positive:0<g)
    (first:bridge ⟨0,by omega⟩=a ⟨m,by omega⟩)
    (last:bridge ⟨g,by omega⟩=b ⟨0,by omega⟩)
    (ε:ℝ)
    (aStep:∀i:ℕ,∀hi:i<m,dist (T (a ⟨i+1,by omega⟩)) (a ⟨i,by omega⟩)<ε)
    (bStep:∀i:ℕ,∀hi:i<n,dist (T (b ⟨i+1,by omega⟩)) (b ⟨i,by omega⟩)<ε)
    (bridgeStep:∀i:ℕ,∀hi:i<g,dist (T (bridge ⟨i+1,by omega⟩)) (bridge ⟨i,by omega⟩)<ε) :
    ∀i:ℕ,∀hi:i<m+g+n,
      dist (T (word a b bridge ⟨i+1,by omega⟩)) (word a b bridge ⟨i,by omega⟩)<ε := by
  intro i hi
  by_cases hprefix:i<m
  · rw [left_index a b bridge _ (show i+1≤m by omega),left_index a b bridge _ (show i≤m by omega)]
    exact aStep i hprefix
  by_cases hmiddle:i<m+g
  · rw [middle_index a b bridge positive first last _ (show m≤ i+1 by omega) (show i+1≤m+g by omega),
      middle_index a b bridge positive first last _ (show m≤ i by omega) (show i≤m+g by omega)]
    have successor:i+1-m=(i-m)+1 := by omega
    simpa only [successor] using bridgeStep (i-m) (by omega)
  · rw [right_index a b bridge positive _ (show m+g≤ i+1 by omega),right_index a b bridge positive _ (show m+g≤ i by omega)]
    have successor:i+1-m-g=(i-m-g)+1 := by omega
    simpa only [successor] using bStep (i-m-g) (by omega)

end LeanShared.FinitePseudoOrbitConcatenation
