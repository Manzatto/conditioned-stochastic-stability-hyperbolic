module

public import Mathlib.Topology.MetricSpace.Thickening

/-! # Uniform separation under small perturbations in compact metric spaces -/

@[expose] public section

open Set Metric

namespace LeanShared

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- If two closed sets meet only inside an open set, sufficiently small
thickenings also meet only inside that open set. -/
theorem exists_thickening_inter_subset_open {A B U : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hU : IsOpen U) (hAB : A ∩ B ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ thickening δ A ∩ thickening δ B ⊆ U := by
  let C : {δ : ℝ // 0 < δ} → Set X := fun δ => cthickening δ.1 A ∩ cthickening δ.1 B
  have hdis : Disjoint (univ \ U) (⋂ δ, C δ) := by
    apply disjoint_left.mpr
    intro x hx hxi
    have hxa : x ∈ A := by
      rw [← hA.closure_eq, closure_eq_iInter_cthickening]
      exact mem_iInter₂.mpr fun δ hδ => (mem_iInter.mp hxi ⟨δ, hδ⟩).1
    have hxb : x ∈ B := by
      rw [← hB.closure_eq, closure_eq_iInter_cthickening]
      exact mem_iInter₂.mpr fun δ hδ => (mem_iInter.mp hxi ⟨δ, hδ⟩).2
    exact hx.2 (hAB ⟨hxa, hxb⟩)
  have hdir : Directed (· ⊇ ·) C := by
    intro a b
    refine ⟨⟨min a.1 b.1, lt_min a.2 b.2⟩, ?_, ?_⟩
    · exact inter_subset_inter (cthickening_mono (min_le_left _ _ ) A)
        (cthickening_mono (min_le_left _ _) B)
    · exact inter_subset_inter (cthickening_mono (min_le_right _ _) A)
        (cthickening_mono (min_le_right _ _) B)
  obtain ⟨δ, hδ⟩ := (isCompact_univ.diff hU).elim_directed_family_closed C
    (fun _ => isClosed_cthickening.inter isClosed_cthickening) hdis hdir
  refine ⟨δ.1, δ.2, ?_⟩
  intro x hx
  by_contra hxU
  exact disjoint_left.mp hδ ⟨mem_univ x, hxU⟩
    ⟨thickening_subset_cthickening _ _ hx.1, thickening_subset_cthickening _ _ hx.2⟩

/-- A deterministic separation property holds for any map uniformly close
on the compact domain. No probability assumptions are required. -/
theorem exists_uniform_nonreturn {T : X → X} {K S U : Set X}
    (hT : Continuous T) (hK : IsCompact K) (hS : IsClosed S) (hU : IsOpen U)
    (hsep : (T '' K) ∩ S ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
      (∀ x ∈ K, dist (F x) (T x) < δ) →
      ∀ x ∈ K, F x ∉ thickening δ S \ U := by
  obtain ⟨δ, hδ, hsub⟩ := exists_thickening_inter_subset_open
    (hK.image hT).isClosed hS hU hsep
  refine ⟨δ, hδ, ?_⟩
  intro F hF x hx hbad
  have himage : F x ∈ thickening δ (T '' K) :=
    mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, hF x hx⟩
  exact hbad.2 (hsub ⟨himage, hbad.1⟩)

end LeanShared
