module
public import LeanShared.Analysis.AnnularDualSupport
public import LeanShared.Analysis.ConstructedBufferedAngularCutoff

/-! The actual enlarged input multipliers. Smoothness, compact support,
and equality to one on the original cone-symbol supports are proved. -/
public noncomputable section
open Set Filter
open scoped ContDiff SchwartzMap Topology
namespace LeanShared.EnlargedConeDyadicSymbols
open ConeDyadicSymbols FourierSchwartzKernel
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def low (χ:RadialCutoff):𝓢(E,ℂ):=
  (2:ℂ) • dilateSymbol (AnnularDualCutoff.radialSymbol χ) 2 (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] in
theorem low_apply (χ:RadialCutoff) (ξ:E):low χ ξ=(χ.toFun (‖ξ‖/2):ℂ):=by
  simp only [low,smul_apply,smul_eq_mul,dilateSymbol_apply]
  change 2*((χ.toFun ‖(2:ℝ)⁻¹ • ξ‖:ℂ)/2)=_
  norm_num [norm_smul,Real.norm_eq_abs,div_eq_mul_inv,mul_comm]
  ring

@[expose] def highFunction (χ:RadialCutoff) (ψ:E→ℝ) (ξ:E):ℂ:=
  AnnularDualCutoff.symbol χ ξ*(ψ (normalized ξ):ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
theorem high_smooth (χ:RadialCutoff) (ψ:E→ℝ) (smooth:ContDiff ℝ ∞ ψ):
    ContDiff ℝ ∞ (highFunction χ ψ):=by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases zero:ξ=0
  · subst ξ
    apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1/4)] with η hη
    have small:‖η‖<1/4:=by simpa only [Metric.mem_ball,dist_zero_right] using hη
    simp only [highFunction,AnnularDualCutoff.collar χ small,zero_mul]
  · exact ((AnnularDualCutoff.symbol χ).smooth ⊤).contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
        (smooth.contDiffAt.comp ξ (normalized_smoothAt zero)))

@[expose] def high (χ:RadialCutoff) (ψ:E→ℝ) (smooth:ContDiff ℝ ∞ ψ):𝓢(E,ℂ):=
  ((AnnularDualCutoff.compact χ).mul_right (f':=fun ξ=>(ψ (normalized ξ):ℂ))).toSchwartzMap
    (high_smooth χ ψ smooth)

@[expose] def symbols (χ:RadialCutoff) (ψ:Bool→E→ℝ)
    (smooth:∀s,ContDiff ℝ ∞ (ψ s)):ℕ × Bool→𝓢(E,ℂ):=
  DyadicSymbols.symbol (fun _=>low χ) (fun s=>high χ (ψ s) (smooth s))

omit [MeasurableSpace E] [BorelSpace E] in
theorem low_compact (χ:RadialCutoff):HasCompactSupport (low (E:=E) χ):=by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) 4)
  intro ξ outside
  have large:4<‖ξ‖:=by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using outside
  rw [low_apply,χ.zero _ (by rw [abs_of_nonneg (by positivity)];linarith),Complex.ofReal_zero]

omit [MeasurableSpace E] [BorelSpace E] in
theorem high_compact (χ:RadialCutoff) (ψ:E→ℝ) (smooth:ContDiff ℝ ∞ ψ):
    HasCompactSupport (high χ ψ smooth):=by
  change HasCompactSupport (fun ξ=>AnnularDualCutoff.symbol χ ξ*(ψ (normalized ξ):ℂ))
  exact (AnnularDualCutoff.compact χ).mul_right

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbols_compact (χ:RadialCutoff) (ψ:Bool→E→ℝ)
    (smooth:∀s,ContDiff ℝ ∞ (ψ s)) (j:ℕ × Bool):
    HasCompactSupport (symbols χ ψ smooth j):=
  DyadicSymbols.symbol_hasCompactSupport (fun _=>low χ) (fun s=>high χ (ψ s) (smooth s))
    (fun _=>low_compact χ) (fun s=>high_compact χ (ψ s) (smooth s)) j

omit [MeasurableSpace E] [BorelSpace E] in
theorem high_base_one {Cp Cm:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
    (ψ:Bool→E→ℝ) (smooth:∀s,ContDiff ℝ ∞ (ψ s))
    (one:∀s ξ,‖ξ‖=1 → (if s then Φ.toFun ξ else 1-Φ.toFun ξ)≠0 → ψ s ξ=1)
    (s:Bool) {ξ:E} (nonzero:ConeDyadicSymbols.high χ Φ.toFun s ξ≠0):
    high χ (ψ s) (smooth s) ξ=1:=by
  have angleNonzero:angle Φ.toFun s ξ≠0:=by
    intro zero
    exact nonzero (by simp only [ConeDyadicSymbols.high,highReal,zero,zero_mul,Complex.ofReal_zero])
  have annularNonzero:annular χ ξ≠0:=by
    intro zero
    exact nonzero (by simp only [ConeDyadicSymbols.high,highReal,zero,mul_zero,Complex.ofReal_zero])
  have lower:1/2≤‖ξ‖:=by
    by_contra! small
    exact annularNonzero (annular_zero_near_origin χ small.le)
  have upper:‖ξ‖≤2:=by
    by_contra! large
    exact annularNonzero (annular_zero_outside χ large.le)
  have ξne:ξ≠0:=by intro zero;rw [zero,norm_zero] at lower;norm_num at lower
  have value:ψ s (normalized ξ)=1:=one s _ (norm_normalized ξne) angleNonzero
  change AnnularDualCutoff.symbol χ ξ*(ψ s (normalized ξ):ℂ)=1
  rw [AnnularDualCutoff.one χ lower upper,value,Complex.ofReal_one,mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
theorem one_on_original {Cp Cm:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
    (ψ:Bool→E→ℝ) (smooth:∀s,ContDiff ℝ ∞ (ψ s))
    (one:∀s ξ,‖ξ‖=1 → (if s then Φ.toFun ξ else 1-Φ.toFun ξ)≠0 → ψ s ξ=1)
    (j:ℕ × Bool) (ξ:E) (nonzero:ConeDyadicSymbols.symbols χ Φ j ξ≠0):
    symbols χ ψ smooth j ξ=1:=by
  change DyadicSymbols.symbol
    (fun _=>FourierSchwartzKernel.symbol (ConeDyadicSymbols.low χ)
      (low_hasCompactSupport χ) (low_smooth χ))
    (fun s=>FourierSchwartzKernel.symbol (ConeDyadicSymbols.high χ Φ.toFun s)
      (high_hasCompactSupport χ Φ.toFun s) (ConeDyadicSymbols.high_smooth χ Φ s)) j ξ≠0 at nonzero
  by_cases zero:j.1=0
  · have original:ConeDyadicSymbols.low χ ξ≠0:=by
      simpa only [DyadicSymbols.symbol,zero,↓reduceIte,FourierSchwartzKernel.symbol_apply] using nonzero
    have bound:‖ξ‖≤2:=by
      by_contra! large
      exact original (by simp only [ConeDyadicSymbols.low,radial_zero_outside χ large.le,
        Complex.ofReal_zero,zero_div])
    change DyadicSymbols.symbol _ _ j ξ=1
    simp only [DyadicSymbols.symbol,zero,↓reduceIte,low_apply]
    rw [χ.one _ (by rw [abs_of_nonneg (by positivity)];linarith),Complex.ofReal_one]
  · have original:ConeDyadicSymbols.high χ Φ.toFun j.2 (((2:ℝ)^j.1)⁻¹ • ξ)≠0:=by
      simpa only [DyadicSymbols.symbol_apply_of_ne_zero _ _ j zero,FourierSchwartzKernel.symbol_apply] using nonzero
    change DyadicSymbols.symbol _ _ j ξ=1
    rw [DyadicSymbols.symbol_apply_of_ne_zero _ _ j zero]
    exact high_base_one χ Φ ψ smooth one j.2 original

omit [MeasurableSpace E] [BorelSpace E] in
theorem multiplier_identity {Cp Cm:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
    (ψ:Bool→E→ℝ) (smooth:∀s,ContDiff ℝ ∞ (ψ s))
    (one:∀s ξ,‖ξ‖=1 → (if s then Φ.toFun ξ else 1-Φ.toFun ξ)≠0 → ψ s ξ=1)
    (j:ℕ × Bool) (ξ:E):
    ConeDyadicSymbols.symbols χ Φ j ξ*symbols χ ψ smooth j ξ=ConeDyadicSymbols.symbols χ Φ j ξ:=by
  by_cases zero:ConeDyadicSymbols.symbols χ Φ j ξ=0
  · simp only [zero,zero_mul]
  · rw [one_on_original χ Φ ψ smooth one j ξ zero,mul_one]
end LeanShared.EnlargedConeDyadicSymbols
