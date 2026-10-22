module
public import LeanShared.Analysis.CloseProjectionRanges

/-! Exact range/kernel dimensions under actual linear coordinate equivalences. -/
public section
namespace LeanShared.ConjugateProjectionRanks
variable {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem range_eq_map (A : H≃L[ℝ]V) (P : H→L[ℝ]H) (Q : V→L[ℝ]V)
    (commutes : ∀v,A (P v)=Q (A v)) : Q.range=P.range.map A.toLinearMap := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    obtain ⟨v,rfl⟩ := A.surjective w
    exact ⟨P v,⟨v,rfl⟩,commutes v⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨A v,(commutes v).symm⟩

theorem ker_eq_map (A : H≃L[ℝ]V) (P : H→L[ℝ]H) (Q : V→L[ℝ]V)
    (commutes : ∀v,A (P v)=Q (A v)) : Q.ker=P.ker.map A.toLinearMap := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,rfl⟩ := A.surjective z
    refine ⟨v,?_,rfl⟩
    change P v=0
    apply A.injective
    rw [commutes,map_zero]
    exact hz
  · rintro ⟨v,hv,rfl⟩
    change Q (A v)=0
    change P v=0 at hv
    rw [←commutes,hv,map_zero]

theorem finrank_range [FiniteDimensional ℝ H] (A : H≃L[ℝ]V)
    (P : H→L[ℝ]H) (Q : V→L[ℝ]V) (commutes : ∀v,A (P v)=Q (A v)) :
    Module.finrank ℝ Q.range=Module.finrank ℝ P.range := by
  rw [range_eq_map A P Q commutes]
  exact A.toLinearEquiv.finrank_map_eq P.range

theorem finrank_ker [FiniteDimensional ℝ H] (A : H≃L[ℝ]V)
    (P : H→L[ℝ]H) (Q : V→L[ℝ]V) (commutes : ∀v,A (P v)=Q (A v)) :
    Module.finrank ℝ Q.ker=Module.finrank ℝ P.ker := by
  rw [ker_eq_map A P Q commutes]
  exact A.toLinearEquiv.finrank_map_eq P.ker

theorem idempotent (A : H≃L[ℝ]V) (P : H→L[ℝ]H) (Q : V→L[ℝ]V)
    (commutes : ∀v,A (P v)=Q (A v)) (idem : ∀v,P (P v)=P v) : ∀z,Q (Q z)=Q z := by
  intro z
  obtain ⟨v,rfl⟩ := A.surjective z
  rw [←commutes,←commutes,idem]
end LeanShared.ConjugateProjectionRanks
