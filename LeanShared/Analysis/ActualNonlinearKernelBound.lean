module
public import LeanShared.Analysis.SharpCenteredNonlinearKernelBound
public import LeanShared.Analysis.NormalizedNonstationaryAmplitudeJets
public import LeanShared.Analysis.NonlinearSymbolPhaseResolution
public import LeanShared.Analysis.CompactUnitMollifier
import Mathlib.Tactic

/-! The actual nonlinear compact Fourier kernel has a sharp fractional
centered envelope, uniformly over arbitrary physical parameters and
bounded dyadic ratios. All coefficient jets and the resolution identity
are constructed internally from the literal map and amplitude controls. -/
public noncomputable section
set_option maxHeartbeats 2000000
open Set MeasureTheory
open scoped ContDiff FourierTransform BoundedContinuousFunction RealInnerProductSpace Pointwise
namespace LeanShared.ActualNonlinearKernelBound
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem exists_bound_of_kernel {P ι:Type*} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
    (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ)
    {κ:E→ℝ} (smoothκ:ContDiff ℝ 1 κ) (compactκ:HasCompactSupport κ)
    (ρ:ℝ) (hρ:0<ρ) (small:Function.support κ⊆Metric.closedBall 0 ρ) (mass:∫y,κ y ∂μ=1)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (χ:Space E→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ)
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (gap:∀p w ζ,g p w≠0→χ ζ≠0→δ≤‖SmoothNonstationarySymbol.gradient
      (fderiv ℝ (G p) w,(s p • (decode ζ).1,t p • (decode ζ).2))‖^2):
    ∃C:ℝ,0≤C ∧∀p,∀Λ:ℝ,1≤Λ→∀a c:ℝ,Λ*s p=a→Λ*t p=c→∀x y:E,
      ‖∫w,𝓕 (fun ζ=>χ ζ*g p w)
        (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (c • (G p w-y))) ∂μ‖≤
      C*(Λ^α)⁻¹*(∫w in L₀+Metric.closedBall 0 ρ,
        envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*c) • (G p w-y)) ∂μ):=by
  have compactg (p:P):HasCompactSupport (fun w=>g p w):=
    compactL₀.of_isClosed_subset (isClosed_tsupport _) (supported p)
  have families (i:ι):=NormalizedNonstationaryAmplitudeJets.exists_family positive hD hH hα hG₀ hG₁
    (b i) (2*m) (decode (E:=E)) (fun p w=>fderiv ℝ (G p) w) value holder
    s t hs ht χ smoothχ compactχ g compactg gvalue gholder
  choose B Q hB hQ q physical compact norms increments using families
  have supportq (p:P) (i:ι):tsupport (fun w=>q i p w)⊆L₀:=by
    apply closure_minimal _ compactL₀.isClosed
    intro w hw
    by_contra hn
    have gz:g p w=0:=image_eq_zero_of_notMem_tsupport (fun h=>hn (supported p h))
    apply hw
    apply Subtype.ext
    apply (BoundedFiniteJetSpace.construct (E:=Space E) (F:=ℂ) (2*m)).faithful
    ext ζ
    rw [physical,gz,mul_zero,zero_mul]
    change 0=(BoundedFiniteJetSpace.construct (E:=Space E) (F:=ℂ) (2*m)).physical 0 ζ
    rw [map_zero]
    rfl
  let f:P→E→Space E→ℂ:=fun p w ζ=>χ ζ*g p w
  have fc (p:P):Continuous (f p).uncurry:=
    (smoothχ.continuous.comp continuous_snd).mul ((g p).continuous.comp continuous_fst)
  have fs (p:P):HasCompactSupport (f p).uncurry:=by
    apply HasCompactSupport.intro (compactL₀.prod compactχ)
    intro wz hwz
    by_cases hw:wz.1∈L₀
    · have hz:wz.2∉tsupport χ:=fun hz=>hwz ⟨hw,hz⟩
      change χ wz.2*g p wz.1=0
      rw [image_eq_zero_of_notMem_tsupport hz,zero_mul]
    · have gz:g p wz.1=0:=image_eq_zero_of_notMem_tsupport (fun h=>hw (supported p h))
      change χ wz.2*g p wz.1=0
      rw [gz,mul_zero]
  apply SharpCenteredNonlinearKernelBound.exists_bound μ m compactχ smoothκ compactκ ρ hρ small mass
    (fun p i=>q i p) compactL₀ supportq hα hD Q hQ
    (fun p i x y=>by simpa only [dist_eq_norm] using increments i p x y)
    G smoothG value s t hs ht b f fc fs
  intro p w ζ
  exact NonlinearSymbolPhaseResolution.resolution b positive
    ((smoothG p).differentiable (by norm_num) w) (s p • (decode ζ).1) (t p • (decode ζ).2)
    (g p w) (χ ζ) (fun i=>SupportedJetFourierEvaluation.physical (2*m) (tsupport χ) (q i p w) ζ)
    (fun i=>physical i p w ζ) (gap p w ζ)
theorem exists_bound {P ι:Type*} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
    (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ)
    (ρ:ℝ) (hρ:0<ρ)
    {δ α D H G₀ G₁:ℝ} (positive:0<δ) (hα:0<α) (hD:0≤D)
    (hH:0≤H) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p))
    (value:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (holder:∀p x y,‖fderiv ℝ (G p) x-fderiv ℝ (G p) y‖≤H*dist x y^α)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (χ:Space E→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ)
    (g:P→E→ᵇℂ) {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p,tsupport (fun w=>g p w)⊆L₀)
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^α)
    (gap:∀p w ζ,g p w≠0→χ ζ≠0→δ≤‖SmoothNonstationarySymbol.gradient
      (fderiv ℝ (G p) w,(s p • (decode ζ).1,t p • (decode ζ).2))‖^2):
    ∃C:ℝ,0≤C ∧∀p,∀Λ:ℝ,1≤Λ→∀a c:ℝ,Λ*s p=a→Λ*t p=c→∀x y:E,
      ‖∫w,𝓕 (fun ζ=>χ ζ*g p w)
        (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (c • (G p w-y))) ∂μ‖≤
      C*(Λ^α)⁻¹*(∫w in L₀+Metric.closedBall 0 ρ,
        envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*c) • (G p w-y)) ∂μ) :=by
  obtain ⟨κ,smoothκ,compactκ,small,mass⟩:=CompactUnitMollifier.exists_kernel_radius μ ρ hρ
  exact exists_bound_of_kernel b μ m smoothκ compactκ ρ hρ small mass positive hα hD hH hG₀ hG₁
    G smoothG value holder s t hs ht χ smoothχ compactχ g compactL₀ supported gvalue gholder gap
end LeanShared.ActualNonlinearKernelBound
