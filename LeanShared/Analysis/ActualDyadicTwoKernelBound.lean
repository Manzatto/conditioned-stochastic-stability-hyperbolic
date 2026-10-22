module
public import LeanShared.Analysis.FiniteTwoKernelFamily
public import LeanShared.Analysis.NormalizedDyadicKernel
public import LeanShared.Analysis.DyadicFrequencyScale
import Mathlib.Tactic

/-! The full dyadic physical kernel estimate. A single constant covers
all frequency levels and cone signs, including both zero-frequency
branches; actual dilation and volume factors are preserved. -/
public noncomputable section
set_option maxHeartbeats 2000000
open Set MeasureTheory
open scoped ContDiff SchwartzMap BoundedContinuousFunction Pointwise
namespace LeanShared.ActualDyadicTwoKernelBound
open HilbertFrequencyPair NormalizedDyadicKernel DyadicFrequencyScale
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_bound {P ι S R:Type*} [Fintype ι] [Fintype S] [Fintype R]
    (b:OrthonormalBasis ι ℝ E) (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ) (ρ:ℝ) (hρ:0<ρ)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (low high:S→𝓢(E,ℂ)) (low' high':R→𝓢(E,ℂ))
    (cl:∀i,HasCompactSupport (low i)) (ch:∀i,HasCompactSupport (high i))
    (cl':∀j,HasCompactSupport (low' j)) (ch':∀j,HasCompactSupport (high' j))
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (good:P→(ℕ × S)→(ℕ × R)→Prop)
    (gap:∀p j k,good p j k→∀w ξ η,g p w≠0→
      DyadicSymbols.symbol low high j (((2:ℝ)^j.1) • ξ)≠0→
      DyadicSymbols.symbol low' high' k (((2:ℝ)^k.1) • η)≠0→
      δ≤‖SmoothNonstationarySymbol.gradient (fderiv ℝ (G p) w,
        (leftRatio j.1 k.1 • ξ,rightRatio j.1 k.1 • η))‖^2):
    ∃C:ℝ,0≤C ∧∀p j k,good p j k→∀x y:E,
      ‖∫w,g p w*DyadicSymbols.kernel low high j (x-w)*
        DyadicSymbols.kernel low' high' k (G p w-y) ∂μ‖≤
      C*(2:ℝ)^(-α*(max j.1 k.1:ℕ))*
        (((2:ℝ)^j.1)^Module.finrank ℝ E*((2:ℝ)^k.1)^Module.finrank ℝ E)*
        (∫w in L₀+Metric.closedBall 0 ρ,
          envelope m (((2*Real.pi)⁻¹*(2:ℝ)^j.1) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*(2:ℝ)^k.1) • (G p w-y)) ∂μ):=by
  let Q:Type _:=P × ((ℕ × S) × (ℕ × R))
  let select:Q→(Bool × S)→(Bool × R)→Prop:=fun p i j=>
    i=index p.2.1 ∧j=index p.2.2 ∧good p.1 p.2.1 p.2.2
  have gapQ:∀p:Q,∀i j,select p i j→∀w ξ η,g p.1 w≠0→
      base low high i ξ≠0→base low' high' j η≠0→
      δ≤‖SmoothNonstationarySymbol.gradient (fderiv ℝ (G p.1) w,
        (leftRatio p.2.1.1 p.2.2.1 • ξ,rightRatio p.2.1.1 p.2.2.1 • η))‖^2:=by
    intro p i j hsel w ξ η hg hξ hη
    rcases hsel with ⟨rfl,rfl,hgood⟩
    exact gap p.1 p.2.1 p.2.2 hgood w ξ η hg
      (by simpa only [symbol_normalization] using hξ)
      (by simpa only [symbol_normalization] using hη)
  obtain ⟨C,hC,bound⟩:=FiniteTwoKernelFamily.exists_bound b μ m ρ hρ positive hα hD hH hG₀ hG₁
    (fun p:Q=>G p.1) (fun p=>smoothG p.1) (fun p=>value p.1) (fun p=>holder p.1)
    (fun p=>leftRatio p.2.1.1 p.2.2.1) (fun p=>rightRatio p.2.1.1 p.2.2.1)
    (fun p=>left_bound _ _) (fun p=>right_bound _ _)
    (base low high) (base low' high') (base_compact low high cl ch) (base_compact low' high' cl' ch')
    (fun p=>g p.1) compactL₀ (fun p=>supported p.1) (fun p=>gvalue p.1) (fun p=>gholder p.1) select gapQ
  refine ⟨C,hC,?_⟩
  intro p j k hgood x y
  have raw:=bound (p,(j,k)) (index j) (index k) ⟨rfl,rfl,hgood⟩
    (major j.1 k.1) (large _ _) ((2:ℝ)^j.1) ((2:ℝ)^k.1)
    (left_identity _ _) (right_identity _ _) x y
  have identity:(∫w,g p w*DyadicSymbols.kernel low high j (x-w)*
      DyadicSymbols.kernel low' high' k (G p w-y) ∂μ)=
      ((((2:ℝ)^j.1)^Module.finrank ℝ E*((2:ℝ)^k.1)^Module.finrank ℝ E:ℝ):ℂ)*
        (∫w,g p w*FourierSchwartzKernel.kernel (base low high (index j)) (((2:ℝ)^j.1) • (x-w))*
          FourierSchwartzKernel.kernel (base low' high' (index k)) (((2:ℝ)^k.1) • (G p w-y)) ∂μ):=by
    simp_rw [kernel_identity,RCLike.real_smul_eq_coe_mul]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    push_cast
    ring
  rw [identity]
  simpa only [DyadicFrequencyScale.decay,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) _)] using raw
end LeanShared.ActualDyadicTwoKernelBound
