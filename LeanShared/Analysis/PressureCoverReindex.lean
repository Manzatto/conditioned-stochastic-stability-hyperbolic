module
public import LeanShared.Analysis.PressureCoverRefinement

/-! Exact invariance of the minimum cylinder cost under a finite-alphabet
reindexing, used for the terminal-label equivalence in the BT comparison. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.PressureCoverReindex
open PressureCoverRefinement
variable {X I J : Type*}

theorem coefficient (e : I ≃ J) (K S : Set X) (u : J → Set X) (f : X → ℝ) :
    coverCoefficient K S (fun i => u (e i)) f = coverCoefficient K S u f := by
  classical
  unfold coverCoefficient
  congr 1
  ext a
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.map e.toEmbedding, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hc hx)
      exact mem_iUnion₂.mpr ⟨e i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, hxi⟩
    · simp only [Finset.sum_map, Equiv.toEmbedding_apply]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.map e.symm.toEmbedding, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hc hx)
      refine mem_iUnion₂.mpr ⟨e.symm j, Finset.mem_map.mpr ⟨j, hj, rfl⟩, ?_⟩
      simpa only [e.apply_symm_apply] using hxj
    · simp only [Finset.sum_map, Equiv.toEmbedding_apply, e.apply_symm_apply]

end LeanShared.PressureCoverReindex
