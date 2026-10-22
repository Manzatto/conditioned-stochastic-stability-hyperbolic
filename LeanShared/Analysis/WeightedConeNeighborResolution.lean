module
public import LeanShared.Analysis.ConeNeighborPhysicalResolution

/-! Exact normalized reconstruction in the actual physical block operators.
The source normalizations are canceled algebraically, before taking norms. -/
public noncomputable section
open Set
open scoped SchwartzMap BigOperators
namespace LeanShared.ConeSymbolOverlap
open ConeDyadicSymbols ConeFourierBlocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm Dp Dm : Set E}

theorem weighted_physical_neighbor_resolution (χ ψ : RadialCutoff)
    (Φ : AngularCutoff Cp Cm) (Ψ : AngularCutoff Dp Dm)
    (weight : (ℕ×Bool)→ℂ) (nonzero : ∀ j,weight j≠0)
    (n : ℕ) (σ : Bool) (f : 𝓢(E,ℂ)) :
    weight (n,σ) • block (symbols χ Φ (n,σ)) f=
      ∑ j∈neighbors n,(weight (n,σ)/weight j) •
        block (symbols χ Φ (n,σ)) (weight j • block (symbols ψ Ψ j) f) := by
  conv_lhs => rw [physical_neighbor_resolution χ ψ Φ Ψ n σ f]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,smul_smul,div_mul_cancel₀ _ (nonzero j)]
end LeanShared.ConeSymbolOverlap
