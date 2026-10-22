module

public import Mathlib.LinearAlgebra.Determinant

/-! Determinants of actual block-diagonal return maps factor under any
complementary coordinate equivalence. Orthogonality or a preferred metric
is not required. -/
public section
namespace LeanShared.ComplementaryDeterminant
variable {R S U E : Type*} [CommRing R] [AddCommGroup S] [Module R S] [Module.Free R S] [Module.Finite R S]
  [AddCommGroup U] [Module R U] [Module.Free R U] [Module.Finite R U]
  [AddCommGroup E] [Module R E]

theorem block (e : (S × U) ≃ₗ[R] E) (A : E →ₗ[R] E) (As : S →ₗ[R] S) (Au : U →ₗ[R] U)
    (action : ∀ s u, A (e (s, u)) = e (As s, Au u)) :
    A.det = As.det * Au.det := by
  have conjugate : e.symm.toLinearMap.comp (A.comp e.toLinearMap) = LinearMap.prodMap As Au := by
    apply LinearMap.ext
    rintro ⟨s, u⟩
    change e.symm (A (e (s, u))) = (As s, Au u)
    rw [action, e.symm_apply_apply]
  have determinant := LinearMap.det_conj A e.symm
  change LinearMap.det (e.symm.toLinearMap.comp (A.comp e.toLinearMap)) = A.det at determinant
  rw [conjugate, LinearMap.det_prodMap] at determinant
  exact determinant.symm

theorem one_sub (e : (S × U) ≃ₗ[R] E) (A : E →ₗ[R] E) (As : S →ₗ[R] S) (Au : U →ₗ[R] U)
    (action : ∀ s u, A (e (s, u)) = e (As s, Au u)) :
    (LinearMap.id - A).det = (LinearMap.id - As).det * (LinearMap.id - Au).det := by
  apply block e
  intro s u
  change e (s, u) - A (e (s, u)) = e (s - As s, u - Au u)
  rw [action, ← map_sub]
  rfl

end LeanShared.ComplementaryDeterminant
