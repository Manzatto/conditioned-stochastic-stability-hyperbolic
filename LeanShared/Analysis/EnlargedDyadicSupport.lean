module
public import LeanShared.Analysis.EnlargedConeDyadicSymbols

/-! Actual normalized radial and angular supports for the enlarged
input symbol, including its independently chosen two angular branches. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.EnlargedDyadicSupport
open ConeDyadicSymbols EnlargedConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalized_support (χ:RadialCutoff) (ψ:Bool→E→ℝ)
    (smooth:∀s,ContDiff ℝ ∞ (ψ s)) (l:ℕ) (s:Bool) (positive:l≠0)
    (η:E) (nonzero:EnlargedConeDyadicSymbols.symbols χ ψ smooth (l,s) (((2:ℝ)^l) • η)≠0):
    1/4<‖η‖ ∧ ‖η‖<4 ∧ ψ s (normalized η)≠0:=by
  change DyadicSymbols.symbol (fun _=>EnlargedConeDyadicSymbols.low χ)
    (fun s=>EnlargedConeDyadicSymbols.high χ (ψ s) (smooth s)) (l,s) (((2:ℝ)^l) • η)≠0 at nonzero
  rw [DyadicSymbols.symbol_apply_of_ne_zero _ _ (l,s) positive] at nonzero
  simp only [inv_smul_smul₀ (pow_ne_zero l (by norm_num : (2:ℝ)≠0))] at nonzero
  change AnnularDualCutoff.symbol χ η*(ψ s (normalized η):ℂ)≠0 at nonzero
  have radial:AnnularDualCutoff.symbol χ η≠0:=by
    intro zero
    exact nonzero (by simp only [zero,zero_mul])
  have angular:ψ s (normalized η)≠0:=by
    intro zero
    exact nonzero (by simp only [zero,Complex.ofReal_zero,mul_zero])
  exact ⟨(AnnularDualCutoff.support_bounds χ radial).1,
    (AnnularDualCutoff.support_bounds χ radial).2,angular⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalized_upper (χ:RadialCutoff) (ψ:Bool→E→ℝ)
    (smooth:∀s,ContDiff ℝ ∞ (ψ s)) (l:ℕ) (s:Bool)
    (η:E) (nonzero:EnlargedConeDyadicSymbols.symbols χ ψ smooth (l,s) (((2:ℝ)^l) • η)≠0):
    ‖η‖≤4:=by
  by_cases zero:l=0
  · subst l
    change EnlargedConeDyadicSymbols.low χ ((1:ℝ) • η)≠0 at nonzero
    rw [one_smul,EnlargedConeDyadicSymbols.low_apply] at nonzero
    by_contra! large
    have h:=χ.zero (‖η‖/2) (by rw [abs_of_nonneg (by positivity)];linarith)
    exact nonzero (by rw [h,Complex.ofReal_zero])
  · exact (normalized_support χ ψ smooth l s zero η nonzero).2.1.le

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalized_outside (χ:RadialCutoff) (ψ:Bool→E→ℝ)
    (smooth:∀s,ContDiff ℝ ∞ (ψ s)) (l:ℕ) (s:Bool) (positive:l≠0)
    (η:E) (nonzero:EnlargedConeDyadicSymbols.symbols χ ψ smooth (l,s) (((2:ℝ)^l) • η)≠0)
    {C:Set E} (scale:∀r:ℝ,0≤r → ∀v∈C,r • v∈C) (support:tsupport (ψ s)⊆Cᶜ):η∉C:=by
  intro inside
  have angular:ψ s (normalized η)≠0:=(normalized_support χ ψ smooth l s positive η nonzero).2.2
  have outside:=support (subset_tsupport _ (Function.mem_support.mpr angular))
  exact outside (scale _ (inv_nonneg.mpr (norm_nonneg _)) _ inside)
end LeanShared.EnlargedDyadicSupport
