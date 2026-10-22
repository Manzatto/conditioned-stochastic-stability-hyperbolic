module
public import LeanShared.Analysis.ConeNeighborResolution
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.OrderedConeSymbolSeparation

/-! Exact finite neighboring-block reconstruction for the physical Fourier
convolution operators, preserving the manuscript's 2π convention. -/
public noncomputable section
open Set
open scoped SchwartzMap FourierTransform BigOperators
namespace LeanShared.ConeSymbolOverlap
open ConeDyadicSymbols ConeFourierBlocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm Dp Dm : Set E}

theorem physical_neighbor_resolution (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm) (n : ℕ) (σ : Bool) (f : 𝓢(E,ℂ)) :
    block (symbols χ Φ (n,σ)) f=∑ j∈neighbors n,
      block (symbols χ Φ (n,σ)) (block (symbols ψ Ψ j) f) := by
  have frequency : 𝓕 (block (symbols χ Φ (n,σ)) f)=
      𝓕 (∑ j∈neighbors n,block (symbols χ Φ (n,σ)) (block (symbols ψ Ψ j) f)) := by
    ext ξ
    simp only [FourierTransform.fourier_sum,sum_apply,fourier_block]
    conv_lhs => rw [neighbor_resolution χ ψ Φ Ψ n σ ((2*Real.pi) • ξ)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have inverse := congrArg (fun g:𝓢(E,ℂ)=>𝓕⁻ g) frequency
  simpa using inverse

theorem physical_plus_minus_zero (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm)
    (ordered : ∀ ξ:E,‖ξ‖=1→ξ∉Dp→ξ∈Cm)
    (n l : ℕ) (positiveN : n≠0) (positiveL : l≠0) (f : 𝓢(E,ℂ)) :
    block (symbols χ Φ (n,true)) (block (symbols ψ Ψ (l,false)) f)=0 := by
  have frequency : 𝓕 (block (symbols χ Φ (n,true)) (block (symbols ψ Ψ (l,false)) f))=0 := by
    ext ξ
    simp only [fourier_block,zero_apply]
    rw [←mul_assoc,OrderedConeSymbolSeparation.plus_minus_zero χ ψ Φ Ψ ordered n l positiveN positiveL,zero_mul]
  have inverse := congrArg (fun g:𝓢(E,ℂ)=>𝓕⁻ g) frequency
  simpa using inverse
end LeanShared.ConeSymbolOverlap
