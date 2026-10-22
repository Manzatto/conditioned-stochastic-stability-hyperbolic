module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! A dense common core identifies finite-dimensional ambient images of
bounded operators. No eigenvector or cross-space comparison is assumed. -/
public section
namespace LeanShared.CommonCoreFiniteImages
variable {E F Z Reg : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem map_range_eq (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    [FiniteDimensional ℂ P.toLinearMap.range] [FiniteDimensional ℂ Q.toLinearMap.range]
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (cA : Reg → E) (cF : Reg → F) (denseA : DenseRange cA) (denseF : DenseRange cF)
    (common : ∀ v, a (P (cA v)) = b (Q (cF v))) :
    P.toLinearMap.range.map a.toLinearMap = Q.toLinearMap.range.map b.toLinearMap := by
  have forward (x : E) : a (P x) ∈ Q.toLinearMap.range.map b.toLinearMap := by
    apply denseA.induction_on (p := fun u => a (P u) ∈ Q.toLinearMap.range.map b.toLinearMap) x
      ((Q.toLinearMap.range.map b.toLinearMap).closed_of_finiteDimensional.preimage
        (a.continuous.comp P.continuous))
    intro v
    rw [common v]
    exact ⟨Q (cF v), ⟨cF v, rfl⟩, rfl⟩
  have backward (y : F) : b (Q y) ∈ P.toLinearMap.range.map a.toLinearMap := by
    apply denseF.induction_on (p := fun u => b (Q u) ∈ P.toLinearMap.range.map a.toLinearMap) y
      ((P.toLinearMap.range.map a.toLinearMap).closed_of_finiteDimensional.preimage
        (b.continuous.comp Q.continuous))
    intro v
    rw [← common v]
    exact ⟨P (cA v), ⟨cA v, rfl⟩, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, ⟨u, rfl⟩, rfl⟩
    exact forward u
  · rintro _ ⟨y, ⟨v, rfl⟩, rfl⟩
    exact backward v
end LeanShared.CommonCoreFiniteImages
