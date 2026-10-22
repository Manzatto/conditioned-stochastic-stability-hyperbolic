module
public import LeanShared.Analysis.FakeLeafGeometry
import all LeanShared.Analysis.FakeLeafGeometry

/-! Translates of the orthogonal complement of any admissible normal plane
satisfy the literal fake-leaf supremum/infimum condition. -/
public section
open Set
namespace LeanShared.FakeLeafGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem planeError_eq_zero_of_orthogonal (P : Submodule ℝ E)
    (positive : 0 < Module.finrank ℝ P) (z : E) (orthogonal : z ∈ Pᗮ) :
    planeError P z=0 := by
  apply le_antisymm _ (planeError_nonneg P z positive)
  apply csSup_le (planeErrorValues_nonempty P z positive)
  rintro r ⟨p,hp,_,rfl⟩
  have innerZero := (Submodule.mem_orthogonal' P z).mp orthogonal p hp
  simp only [normalized,inner_smul_left,inner_smul_right,innerZero,mul_zero,le_refl,map_inv₀,
    conj_trivial]

theorem normalError_eq_zero_of_admissible_orthogonal {C : Set E} {ds : ℕ}
    (positive : 0 < ds) (P : Submodule ℝ E) (admissible : P ∈ admissiblePlanes C ds)
    (z : E) (orthogonal : z ∈ Pᗮ) : normalError C ds z=0 := by
  apply le_antisymm _ (normalError_nonneg positive ⟨P,admissible⟩ z)
  have upper := csInf_le (normalErrorValues_bddBelow C positive z)
    (show planeError P z ∈ normalErrorValues C ds z from ⟨P,admissible,rfl⟩)
  exact upper.trans_eq (planeError_eq_zero_of_orthogonal P (admissible.2.symm ▸ positive) z orthogonal)

theorem leafError_eq_zero_of_admissible_chords {C : Set E} {ds : ℕ}
    (positive : 0 < ds) (P : Submodule ℝ E) (admissible : P ∈ admissiblePlanes C ds)
    (Γ : Set E) (chords : ∀ x ∈ Γ, ∀ y ∈ Γ, y-x ∈ Pᗮ) : leafError C ds Γ=0 := by
  have zeroValue : ∀ r ∈ leafErrorValues C ds Γ, r=0 := by
    rintro r ⟨x,hx,y,hy,_,rfl⟩
    exact normalError_eq_zero_of_admissible_orthogonal positive P admissible (y-x) (chords x hx y hy)
  by_cases nonempty : (leafErrorValues C ds Γ).Nonempty
  · apply le_antisymm
    · exact csSup_le nonempty (fun r hr => (zeroValue r hr).le)
    · obtain ⟨r,hr⟩ := nonempty
      rw [← zeroValue r hr]
      exact le_csSup (leafErrorValues_bddAbove positive ⟨P,admissible⟩ Γ) hr
  · have empty := Set.not_nonempty_iff_eq_empty.mp nonempty
    simp only [leafError,empty,Real.sSup_empty]

/-- An affine plane is used literally, with arbitrary transverse translation. -/
theorem leafError_affine_orthogonal {C : Set E} {ds : ℕ}
    (positive : 0 < ds) (P : Submodule ℝ E) (admissible : P ∈ admissiblePlanes C ds)
    (a : E) : leafError C ds ((fun v : Pᗮ => (v:E)+a) '' univ)=0 := by
  apply leafError_eq_zero_of_admissible_chords positive P admissible
  rintro x ⟨u,_,rfl⟩ y ⟨v,_,rfl⟩
  simpa only [add_sub_add_right_eq_sub] using (Pᗮ).sub_mem v.property u.property
end LeanShared.FakeLeafGeometry
