module
public import LeanShared.Analysis.ActualTwoKernelBound
import Mathlib.Tactic

/-! Uniform sharp physical kernel bounds for a finite family of actual
low/high and cone-sign bases. Separation is only required for the
selected nonlinked parameters, with no topology on those parameters. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff SchwartzMap BoundedContinuousFunction Pointwise
namespace LeanShared.FiniteTwoKernelFamily
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_bound {P ι I J:Type*} [Fintype ι] [Fintype I] [Fintype J]
    (b:OrthonormalBasis ι ℝ E) (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ) (ρ:ℝ) (hρ:0<ρ)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (σ:I→𝓢(E,ℂ)) (τ:J→𝓢(E,ℂ))
    (compactσ:∀i,HasCompactSupport (σ i)) (compactτ:∀j,HasCompactSupport (τ j))
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (good:P→I→J→Prop)
    (gap:∀p i j,good p i j→∀w ξ η,g p w≠0→σ i ξ≠0→τ j η≠0→
      δ≤‖SmoothNonstationarySymbol.gradient (fderiv ℝ (G p) w,(s p • ξ,t p • η))‖^2):
    ∃C:ℝ,0≤C ∧∀p i j,good p i j→∀Λ:ℝ,1≤Λ→∀a c:ℝ,Λ*s p=a→Λ*t p=c→∀x y:E,
      ‖((a^Module.finrank ℝ E*c^Module.finrank ℝ E:ℝ):ℂ)*
        (∫w,g p w*FourierSchwartzKernel.kernel (σ i) (a • (x-w))*
          FourierSchwartzKernel.kernel (τ j) (c • (G p w-y)) ∂μ)‖≤
      C*(Λ^α)⁻¹*(|a|^Module.finrank ℝ E*|c|^Module.finrank ℝ E)*
        (∫w in L₀+Metric.closedBall 0 ρ,envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*c) • (G p w-y)) ∂μ):=by
  have component (ij:I × J):=ActualTwoKernelBound.exists_scaled_bound (P:={p:P //good p ij.1 ij.2})
    b μ m ρ hρ positive hα hD hH hG₀ hG₁
    (fun p=>G p.val) (fun p=>smoothG p.val) (fun p=>value p.val) (fun p=>holder p.val)
    (fun p=>s p.val) (fun p=>t p.val) (fun p=>hs p.val) (fun p=>ht p.val)
    (σ ij.1) (τ ij.2) (compactσ ij.1) (compactτ ij.2)
    (fun p=>g p.val) compactL₀ (fun p=>supported p.val) (fun p=>gvalue p.val) (fun p=>gholder p.val)
    (fun p=>gap p.val ij.1 ij.2 p.property)
  choose C hC bound using component
  refine ⟨∑ij,C ij,Finset.sum_nonneg (fun ij _=>hC ij),?_⟩
  intro p i j goodp Λ large a c ha hc x y
  have raw:=bound (i,j) ⟨p,goodp⟩ Λ large a c ha hc x y
  have leC:C (i,j)≤∑ij,C ij:=Finset.single_le_sum (fun ij _=>hC ij) (Finset.mem_univ _)
  have decay:0≤(Λ^α)⁻¹:=inv_nonneg.mpr (Real.rpow_nonneg (zero_lt_one.trans_le large).le α)
  exact raw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right leC decay) (by positivity))
    (integral_nonneg (fun w=>by dsimp [envelope];positivity)))
end LeanShared.FiniteTwoKernelFamily
