module
public import LeanShared.Analysis.ActualNonlinearKernelBound
public import LeanShared.Analysis.PhysicalTwoKernelIdentity
import Mathlib.Tactic

/-! Sharp fractional decay for the literal two-convolution nonlinear
transfer kernel, with the manuscript's physical Fourier normalization.
No frequency-jet, regularized-identity or kernel-decay source is assumed. -/
public noncomputable section
set_option maxHeartbeats 1500000
open Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap BoundedContinuousFunction RealInnerProductSpace Pointwise
namespace LeanShared.ActualTwoKernelBound
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_bound {P ι:Type*} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
    (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ) (ρ:ℝ) (hρ:0<ρ)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (σ τ:𝓢(E,ℂ)) (compactσ:HasCompactSupport σ) (compactτ:HasCompactSupport τ)
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (gap:∀p w ξ η,g p w≠0→σ ξ≠0→τ η≠0→δ≤‖SmoothNonstationarySymbol.gradient
      (fderiv ℝ (G p) w,(s p • ξ,t p • η))‖^2):
    ∃C:ℝ,0≤C ∧∀p,∀Λ:ℝ,1≤Λ→∀a c:ℝ,Λ*s p=a→Λ*t p=c→∀x y:E,
      ‖∫w,g p w*FourierSchwartzKernel.kernel σ (a • (x-w))*
        FourierSchwartzKernel.kernel τ (c • (G p w-y)) ∂μ‖≤
      C*(Λ^α)⁻¹*(∫w in L₀+Metric.closedBall 0 ρ,
        envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*c) • (G p w-y)) ∂μ):=by
  let χ:Space E→ℂ:=fun ζ=>σ (decode ζ).1*τ (decode ζ).2
  have smoothχ:ContDiff ℝ ∞ χ:=PhysicalTwoKernelIdentity.product_smooth σ τ
  have compactχ:HasCompactSupport χ:=PhysicalTwoKernelIdentity.product_compact σ τ compactσ compactτ
  have gapχ (p:P) (w:E) (ζ:Space E) (hg:g p w≠0) (hc:χ ζ≠0):
      δ≤‖SmoothNonstationarySymbol.gradient
        (fderiv ℝ (G p) w,(s p • (decode ζ).1,t p • (decode ζ).2))‖^2:=by
    exact gap p w _ _ hg (mul_ne_zero_iff.mp hc).1 (mul_ne_zero_iff.mp hc).2
  obtain ⟨C,hC,bound⟩:=ActualNonlinearKernelBound.exists_bound b μ m ρ hρ positive hα hD hH hG₀ hG₁
    G smoothG value holder s t hs ht χ smoothχ compactχ g compactL₀ supported gvalue gholder gapχ
  let N:ℝ:=FourierSchwartzKernel.normalization (E:=E)
  have hN:0<N:=FourierSchwartzKernel.normalization_pos
  have normN:‖(N:ℂ)^2‖=N^2:=by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  refine ⟨N^2*C,mul_nonneg (sq_nonneg N) hC,?_⟩
  intro p Λ large a c ha hc x y
  have scalar (w:E) (z:Space E):𝓕 (fun ζ=>χ ζ*g p w) z=𝓕 χ z*g p w:=by
    simp only [Real.fourier_eq',smul_eq_mul,←mul_assoc]
    exact integral_mul_const _ _
  have pointwise (w:E):g p w*FourierSchwartzKernel.kernel σ (a • (x-w))*
      FourierSchwartzKernel.kernel τ (c • (G p w-y))=
      (N:ℂ)^2*𝓕 (fun ζ=>χ ζ*g p w)
        (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (c • (G p w-y))):=by
    rw [scalar]
    have identity:=PhysicalTwoKernelIdentity.product_identity σ τ (a • (x-w)) (c • (G p w-y))
    change (N:ℂ)^2*𝓕 χ (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (c • (G p w-y)))=_ at identity
    calc
      _ = g p w*(FourierSchwartzKernel.kernel σ (a • (x-w))*
          FourierSchwartzKernel.kernel τ (c • (G p w-y))):=by ring
      _ = _:=by rw [←identity];ring
  simp_rw [pointwise]
  rw [integral_const_mul,norm_mul,normN]
  exact (mul_le_mul_of_nonneg_left (bound p Λ large a c ha hc x y) (sq_nonneg N)).trans_eq (by ring)
theorem exists_scaled_bound {P ι:Type*} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
    (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ) (ρ:ℝ) (hρ:0<ρ)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (σ τ:𝓢(E,ℂ)) (compactσ:HasCompactSupport σ) (compactτ:HasCompactSupport τ)
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (gap:∀p w ξ η,g p w≠0→σ ξ≠0→τ η≠0→δ≤‖SmoothNonstationarySymbol.gradient
      (fderiv ℝ (G p) w,(s p • ξ,t p • η))‖^2):
    ∃C:ℝ,0≤C ∧∀p,∀Λ:ℝ,1≤Λ→∀a c:ℝ,Λ*s p=a→Λ*t p=c→∀x y:E,
      ‖((a^Module.finrank ℝ E*c^Module.finrank ℝ E:ℝ):ℂ)*(∫w,g p w*FourierSchwartzKernel.kernel σ (a • (x-w))*
        FourierSchwartzKernel.kernel τ (c • (G p w-y)) ∂μ)‖≤
      C*(Λ^α)⁻¹*(|a|^Module.finrank ℝ E*|c|^Module.finrank ℝ E)*(∫w in L₀+Metric.closedBall 0 ρ,
        envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*c) • (G p w-y)) ∂μ) :=by
  obtain ⟨C,hC,bound⟩:=exists_bound b μ m ρ hρ positive hα hD hH hG₀ hG₁
    G smoothG value holder s t hs ht σ τ compactσ compactτ g compactL₀ supported gvalue gholder gap
  refine ⟨C,hC,?_⟩
  intro p Λ large a c ha hc x y
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_pow]
  exact (mul_le_mul_of_nonneg_left (bound p Λ large a c ha hc x y) (by positivity)).trans_eq (by ring)
end LeanShared.ActualTwoKernelBound
