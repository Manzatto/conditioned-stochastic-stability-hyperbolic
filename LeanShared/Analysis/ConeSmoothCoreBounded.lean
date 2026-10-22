module
public import LeanShared.Analysis.DyadicHigherHolderCoreBounded
public import LeanShared.Analysis.ConeDyadicSymbols

/-! Every finite pair of real anisotropic exponents has a bounded actual
supported smooth core. A sufficient higher regularity order is constructed
from those exponents, so no smooth-core boundedness premise remains. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology
namespace LeanShared.ConeSmoothCoreBounded
open ConeDyadicSymbols
variable {E : Type} {U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ:Measure U) [μ.IsAddHaarMeasure] {J:ℝ} (hJ:0≤J)
  (leaves:A→GraphLeafNorm.GraphLeaf U E J)
  {Cp Cm:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cp Cm)
  {K:Set E} (compact:IsCompact K) (t:Bool→ℝ)

include compact in
theorem smoothCoreBounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K (symbols χ Φ) t := by
  classical
  let lowBase : Bool→𝓢(E,ℂ) := fun _=>FourierSchwartzKernel.symbol
    (low χ) (low_hasCompactSupport χ) (low_smooth χ)
  let highBase : Bool→𝓢(E,ℂ) := fun s=>FourierSchwartzKernel.symbol
    (high χ Φ.toFun s) (high_hasCompactSupport χ Φ.toFun s) (high_smooth χ Φ s)
  have zero (s:Bool) : ∀ᶠ ξ in 𝓝 (0:E),highBase s ξ=0 := by
    filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1/2)] with ξ small
    have size : ‖ξ‖≤1/2 := by simpa only [Metric.mem_ball,dist_zero_right] using (Metric.mem_ball.mp small).le
    change high χ Φ.toFun s ξ=0
    rw [high,highReal,annular_zero_near_origin χ size,mul_zero,Complex.ofReal_zero]
  let n := Finset.univ.sup (fun s:Bool=>⌈t s⌉₊)
  have margin (s:Bool) : t s≤(1/2:ℝ)+(n+1:ℕ) := by
    have hi : ⌈t s⌉₊≤n := Finset.le_sup (f:=fun s:Bool=>⌈t s⌉₊) (Finset.mem_univ s)
    have hr : (⌈t s⌉₊:ℝ)≤(n:ℝ) := by exact_mod_cast hi
    have hc := Nat.le_ceil (t s)
    push_cast
    linarith
  exact DyadicHigherHolderCoreBounded.smoothCoreBounded (stdOrthonormalBasis ℝ E) μ hJ leaves
    lowBase highBase zero compact (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
    n t margin
end LeanShared.ConeSmoothCoreBounded
