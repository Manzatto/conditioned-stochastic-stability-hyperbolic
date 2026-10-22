module
public import LeanShared.Analysis.WeightedConeNeighborResolution
public import LeanShared.Analysis.ConeAnisotropicWeights

/-! Finite neighboring physical blocks give a uniform anisotropic comparison.
Only the actual convolution estimate is supplied; forbidden sign terms vanish
by the proved physical multiplier identity. -/
public noncomputable section
open Set
open scoped SchwartzMap BigOperators
namespace LeanShared.ConeSymbolOverlap
open ConeDyadicSymbols ConeFourierBlocks
variable {E B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup B] [NormedSpace ℂ B] {Cp Cm Dp Dm : Set E}

theorem normalized_row_norm_le (χ ψ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (Ψ : AngularCutoff Dp Dm) (ordered : ∀ ξ:E,‖ξ‖=1→ξ∉Dp→ξ∈Cm)
    (t s:ℝ) (order : s≤t) (realize : 𝓢(E,ℂ)→ₗ[ℂ]B)
    (A N:ℝ) (nonnegativeA : 0≤A) (nonnegativeN : 0≤N)
    (n:ℕ) (σ:Bool) (f:𝓢(E,ℂ))
    (convolve : ∀ j∈neighbors n,
      ‖realize (block (symbols χ Φ (n,σ))
        (anisotropicWeight t s j • block (symbols ψ Ψ j) f))‖≤A*N) :
    ‖realize (anisotropicWeight t s (n,σ) • block (symbols χ Φ (n,σ)) f)‖≤
      6*A*((2:ℝ)^(3*(|s|+|t|)))*N := by
  classical
  let R := (2:ℝ)^(3*(|s|+|t|))
  have positiveR : 0≤R := (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [weighted_physical_neighbor_resolution χ ψ Φ Ψ (anisotropicWeight t s)
    (anisotropicWeight_nonzero t s),map_sum]
  have point (j:ℕ×Bool) (hj:j∈neighbors n) :
      ‖realize ((anisotropicWeight t s (n,σ)/anisotropicWeight t s j) •
        block (symbols χ Φ (n,σ)) (anisotropicWeight t s j • block (symbols ψ Ψ j) f))‖≤R*(A*N) := by
    have close : n≤j.1+1 ∧ j.1≤n+1 := by
      simp only [neighbors,Finset.mem_product,Finset.mem_Icc,Finset.mem_univ,and_true] at hj
      omega
    by_cases forbidden : σ=true ∧ j.2=false ∧ 1<n
    · obtain ⟨rfl,sign,large⟩ := forbidden
      have nonzeroN : n≠0 := by omega
      have nonzeroL : j.1≠0 := by omega
      have zeroBlock : block (symbols χ Φ (n,true)) (block (symbols ψ Ψ j) f)=0 := by
        rcases j with ⟨l,τ⟩
        change τ=false at sign
        subst τ
        exact physical_plus_minus_zero χ ψ Φ Ψ ordered n l nonzeroN nonzeroL f
      rw [map_smul,map_smul,map_smul,zeroBlock,map_zero,smul_zero,smul_zero,norm_zero]
      positivity
    · have allowed : σ=true→j.2=false→n≤1 := by
        intro hs ht
        by_contra hn
        exact forbidden ⟨hs,ht,by omega⟩
      have ratio := neighbor_weight_bound t s order n j.1 σ j.2 close allowed
      rw [map_smul,norm_smul,anisotropicWeight_ratio_norm]
      exact mul_le_mul ratio (convolve j hj) (norm_nonneg _) positiveR
  have sumBound := (norm_sum_le _ _).trans (Finset.sum_le_sum point)
  have card : ((neighbors n).card:ℝ)≤6 := by exact_mod_cast neighbors_card_le n
  have bound := mul_le_mul_of_nonneg_right card (mul_nonneg positiveR (mul_nonneg nonnegativeA nonnegativeN))
  simp only [Finset.sum_const,nsmul_eq_mul] at sumBound
  nlinarith
end LeanShared.ConeSymbolOverlap
