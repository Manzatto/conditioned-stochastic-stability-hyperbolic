module
public import LeanShared.Analysis.FakeLeafLinearImage

/-! Enlarging the actual cotangent cone enlarges the manuscript's literal
fake-leaf family. The infimum-over-planes condition is preserved without
choosing minimizing normal planes. -/
public section
open Set
namespace LeanShared.FakeLeafGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem admissiblePlanes_mono {C D : Set E} (inside : C⊆D) (ds : ℕ) :
    admissiblePlanes C ds⊆admissiblePlanes D ds := by
  intro P hP
  exact ⟨hP.1.trans inside,hP.2⟩

theorem normalError_antitone {C D : Set E} {ds : ℕ} (inside : C⊆D)
    (positive : 0<ds) (planes : (admissiblePlanes C ds).Nonempty) (z : E) :
    normalError D ds z≤normalError C ds z := by
  apply csInf_le_csInf (normalErrorValues_bddBelow D positive z)
    (normalErrorValues_nonempty planes z)
  exact image_mono (admissiblePlanes_mono inside ds)

theorem leafError_zero_mono {C D Γ : Set E} {ds : ℕ} (inside : C⊆D)
    (positive : 0<ds) (planes : (admissiblePlanes C ds).Nonempty)
    (zero : leafError C ds Γ=0) : leafError D ds Γ=0 := by
  have targetPlanes : (admissiblePlanes D ds).Nonempty := planes.mono (admissiblePlanes_mono inside ds)
  apply FakeLeafLinearImage.leafError_zero_of_chords positive targetPlanes
  intro x hx y hy different
  apply le_antisymm
  · exact (normalError_antitone inside positive planes (y-x)).trans_eq
      (normalError_eq_zero_of_leafError_zero positive planes zero hx hy different)
  · exact normalError_nonneg positive targetPlanes _
end LeanShared.FakeLeafGeometry
