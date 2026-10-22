module

public import LeanShared.Analysis.ConeDyadicSymbols

/-! A smooth cone cutoff can be chosen even by symmetrization when both
cones are invariant under negation. This preserves the actual cone values. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Cp Cm : Set E}

def AngularCutoff.evenize (Φ : AngularCutoff Cp Cm)
    (hp : ∀ x ∈ Cp, -x ∈ Cp) (hm : ∀ x ∈ Cm, -x ∈ Cm) : AngularCutoff Cp Cm where
  toFun x := (Φ.toFun x + Φ.toFun (-x)) / 2
  smoothAt_unit x hx := ((Φ.smoothAt_unit x hx).add
    ((Φ.smoothAt_unit (-x) (by simpa using hx)).comp x contDiffAt_id.neg)).div_const 2
  nonneg_unit x hx := div_nonneg (add_nonneg (Φ.nonneg_unit x hx)
    (Φ.nonneg_unit (-x) (by simpa using hx))) (by norm_num)
  le_one_unit x hx := by
    have h1 := Φ.le_one_unit x hx
    have h2 := Φ.le_one_unit (-x) (by simpa using hx)
    linarith
  one_on x hx hn := by rw [Φ.one_on x hx hn, Φ.one_on (-x) (hp x hx) (by simpa using hn)]; norm_num
  zero_on x hx hn := by rw [Φ.zero_on x hx hn, Φ.zero_on (-x) (hm x hx) (by simpa using hn)]; norm_num

@[simp] theorem AngularCutoff.evenize_even (Φ : AngularCutoff Cp Cm)
    (hp : ∀ x ∈ Cp, -x ∈ Cp) (hm : ∀ x ∈ Cm, -x ∈ Cm) (x : E) :
    (Φ.evenize hp hm).toFun (-x) = (Φ.evenize hp hm).toFun x := by
  simp only [evenize, neg_neg]
  rw [add_comm]

end LeanShared.ConeDyadicSymbols
