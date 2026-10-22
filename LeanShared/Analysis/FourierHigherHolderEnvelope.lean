module
public import LeanShared.Analysis.FourierHigherRadialEnvelope
public import LeanShared.Geometry.HigherHolderConstructedBounds

/-! Uniform higher-order fractional Fourier decay controlled by the actual
constructed Banach graph norm, rather than an independent Holder constant. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BoundedContinuousFunction
namespace LeanShared.FourierHigherHolderEnvelope
open FourierSchwartzKernel HigherDerivativeHolderSpace
variable {E ι:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] (b:OrthonormalBasis ι ℝ E)

include b in
theorem exists_envelope (σ:𝓢(E,ℂ)) (zero:∀ᶠξ in 𝓝 (0:E),σ ξ=0)
    {K:Set E} (compact:IsCompact K) {a:ℝ} (ha:0<a) (ha1:a<1) (n m:ℕ) :
    ∃B:ℝ,0≤B ∧ ∀v:(constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).carrier,
      tsupport ((constructFull ha ha1 (n+1)).physical v)⊆K→
      ∀r:ℝ,∀hr:1≤r,∀x:E,
      ‖∫y,kernel (dilateSymbol σ r (by linarith)) y*
        (constructFull ha ha1 (n+1)).physical v (x-y)‖≤
        B*‖v‖*(r^(a+(n+1:ℕ)))⁻¹*GraphLeafNorm.radialWeight (m:ℝ) x := by
  obtain ⟨B,hB,bound⟩:=FourierHigherRadialEnvelope.exists_envelope b σ zero compact ha.le n m
  refine ⟨B,hB,?_⟩
  intro v support r hr x
  have regular:=(constructFull ha ha1 (n+1)).regular v
  have order:n+1≤⌊a+(n+1:ℕ)⌋₊:=Nat.le_floor (by linarith)
  have smooth:ContDiff ℝ (n+1) ((constructFull ha ha1 (n+1)).physical v):=
    regular.differentiable.contDiff.of_le (by exact_mod_cast order)
  exact bound _ ‖v‖ (norm_nonneg v) smooth support
    (constructed_full_increment ha ha1 (n+1) v) r hr x
end LeanShared.FourierHigherHolderEnvelope
