module
public import LeanShared.Analysis.ConeSymbolOverlap

/-! A target cone multiplier is recovered exactly from the neighboring
levels of any source cone resolution. No infinite-tail estimate is assumed. -/
public noncomputable section
open Set
open scoped SchwartzMap BigOperators
namespace LeanShared.ConeSymbolOverlap
open ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm Dp Dm : Set E}

@[expose] def neighbors (n:ℕ) : Finset (ℕ×Bool) :=
  Finset.Icc (n-1) (n+1) ×ˢ Finset.univ

theorem neighbor_resolution (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm) (n : ℕ) (σ : Bool) (ξ : E) :
    symbols χ Φ (n,σ) ξ=∑ j∈neighbors n,
      symbols χ Φ (n,σ) ξ*symbols ψ Ψ j ξ := by
  classical
  have zero (j:ℕ×Bool) (outside:j∉neighbors n) :
      symbols χ Φ (n,σ) ξ*symbols ψ Ψ j ξ=0 := by
    have far : n+1<j.1 ∨ j.1+1<n := by
      simp only [neighbors,Finset.mem_product,Finset.mem_Icc,Finset.mem_univ,and_true,not_and_or] at outside
      omega
    exact product_zero_of_far χ ψ Φ Ψ n j.1 σ j.2 ξ far
  have finite : HasSum (fun j:ℕ×Bool=>symbols χ Φ (n,σ) ξ*symbols ψ Ψ j ξ)
      (∑ j∈neighbors n,symbols χ Φ (n,σ) ξ*symbols ψ Ψ j ξ) :=
    hasSum_sum_of_ne_finset_zero (s:=neighbors n) zero
  have complete := (ConeDyadicResolution.hasSum_symbols ψ Ψ ξ).mul_left (symbols χ Φ (n,σ) ξ)
  simpa only [mul_one] using complete.unique finite
end LeanShared.ConeSymbolOverlap
