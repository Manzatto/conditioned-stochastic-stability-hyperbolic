module
public import LeanShared.Analysis.CommonAmbientShiftPowers

/-! Equality of stabilized generalized images implies equality at every
finite Jordan order, by the actual common ambient action and injectivity. -/
public section
namespace LeanShared.CommonAmbientStableKernels
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem map_eq (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (actionA : a.comp P = L.comp a) (actionB : b.comp Q = L.comp b)
    (injectiveA : Function.Injective a) (injectiveB : Function.Injective b)
    (z : ℂ) (n m : ℕ)
    (stableP : ∀ k, ((P-z•1)^(n+k)).ker = ((P-z•1)^n).ker)
    (stableQ : ∀ k, ((Q-z•1)^(m+k)).ker = ((Q-z•1)^m).ker)
    (images : ((P-z•1)^n).ker.map a.toLinearMap = ((Q-z•1)^m).ker.map b.toLinearMap)
    (k : ℕ) : ((P-z•1)^k).ker.map a.toLinearMap = ((Q-z•1)^k).ker.map b.toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have stable : x ∈ ((P-z•1)^n).ker := by
      rw [←stableP k]
      change ((P-z•1)^(n+k)) x = 0
      rw [pow_add,mul_apply_eq_comp,show ((P-z•1)^k) x=0 from hx,map_zero]
    have member : a x ∈ ((Q-z•1)^m).ker.map b.toLinearMap := by
      rw [←images]
      exact ⟨x,stable,rfl⟩
    rcases member with ⟨y,_,same⟩
    refine ⟨y,?_,same⟩
    exact CommonAmbientShiftPowers.kernel_mem_of_match P Q L a b actionA actionB injectiveB
      z k x y same.symm hx
  · rintro _ ⟨y,hy,rfl⟩
    have stable : y ∈ ((Q-z•1)^m).ker := by
      rw [←stableQ k]
      change ((Q-z•1)^(m+k)) y = 0
      rw [pow_add,mul_apply_eq_comp,show ((Q-z•1)^k) y=0 from hy,map_zero]
    have member : b y ∈ ((P-z•1)^n).ker.map a.toLinearMap := by
      rw [images]
      exact ⟨y,stable,rfl⟩
    rcases member with ⟨x,_,same⟩
    refine ⟨x,?_,same⟩
    exact CommonAmbientShiftPowers.kernel_mem_of_match Q P L b a actionB actionA injectiveA
      z k y x same.symm hy
end LeanShared.CommonAmbientStableKernels
