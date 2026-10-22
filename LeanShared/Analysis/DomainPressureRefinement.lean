module

public import LeanShared.Analysis.PressureCoverRefinement

/-! # Pressure-cover refinement with only valid-cylinder boundedness

Selecting and shrinking an open source pressure cover only uses boundedness
on its individual cylinders. Global continuity of a chart-defined density
is unnecessary. Such boundedness follows from continuity on a valid compact
outer closure; nearby-word continuity is handled separately.
-/

@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.DomainPressureRefinement
open PressureCoverRefinement
variable {X I : Type*} [TopologicalSpace X]

/-- A valid compact outer cylinder supplies boundedness on its open inner
cylinder, without continuity outside the chart domain. -/
theorem domainValues_bddAbove_of_valid_closure
    {K A : Set X} {f : X → ℝ} (hK : IsCompact K)
    (hf : ContinuousOn f (K ∩ closure A)) : BddAbove ({0} ∪ f '' (K ∩ A)) := by
  exact (isCompact_singleton.union
    ((hK.inter_right isClosed_closure).image_of_continuousOn hf)).bddAbove.mono
    (union_subset_union_right _ (image_mono (inter_subset_inter_right K subset_closure)))

omit [TopologicalSpace X] in
theorem domainCoefficient_nonneg_of_bdd {K A : Set X} {f : X → ℝ}
    (hb : BddAbove ({0} ∪ f '' (K ∩ A))) : 0 ≤ domainCoefficient K A f :=
  le_csSup hb (Or.inl (mem_singleton 0))

omit [TopologicalSpace X] in
theorem domainCoefficient_mono_of_bdd {K A B : Set X} {f : X → ℝ}
    (hb : BddAbove ({0} ∪ f '' (K ∩ B))) (hAB : A ⊆ B) :
    domainCoefficient K A f ≤ domainCoefficient K B f := by
  exact csSup_le_csSup hb (show ({0} ∪ f '' (K ∩ A) : Set ℝ).Nonempty from
    ⟨0, Or.inl (mem_singleton 0)⟩)
    (union_subset_union_right _ (image_mono (inter_subset_inter_right K hAB)))

omit [TopologicalSpace X] in
theorem coverCoefficient_nonneg_of_bdd {K S : Set X} {u : I → Set X} {f : X → ℝ}
    (hb : ∀ i, BddAbove ({0} ∪ f '' (K ∩ u i)))
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i) :
    0 ≤ coverCoefficient K S u f := by
  obtain ⟨c, hc⟩ := hcover
  apply le_csInf (s := {b | ∃ d : Finset I, S ⊆ ⋃ i ∈ d, u i ∧
    b = ∑ i ∈ d, domainCoefficient K (u i) f})
    (show ({b | ∃ d : Finset I, S ⊆ ⋃ i ∈ d, u i ∧
      b = ∑ i ∈ d, domainCoefficient K (u i) f} : Set ℝ).Nonempty from ⟨_, c, hc, rfl⟩)
  rintro b ⟨d, _, rfl⟩
  exact Finset.sum_nonneg fun i _ => domainCoefficient_nonneg_of_bdd (hb i)

variable [T2Space X] [LocallyCompactSpace X]

theorem exists_refined_pressure_cover_of_bdd
    {K S : Set X} {f : X → ℝ} {a : ℝ} (hS : IsCompact S)
    (u : I → Set X) (hu : ∀ i, IsOpen (u i))
    (hb : ∀ i, BddAbove ({0} ∪ f '' (K ∩ u i)))
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i)
    (hstrict : coverCoefficient K S u f < a) :
    ∃ (c : Finset I) (v : c → Set X),
      S ⊆ ⋃ i, v i ∧ (∀ i, IsOpen (v i)) ∧
      (∀ i, IsCompact (closure (v i))) ∧ (∀ i, closure (v i) ⊆ u i) ∧
      (∑ i, domainCoefficient K (closure (v i)) f) < a := by
  classical
  obtain ⟨c, hc, hcost⟩ := exists_cover_cost_lt hcover hstrict
  have hcover' : S ⊆ ⋃ i : c, u i := by
    intro x hx
    obtain ⟨i, hic, hxi⟩ := mem_iUnion₂.mp (hc hx)
    exact mem_iUnion.mpr ⟨⟨i, hic⟩, hxi⟩
  obtain ⟨v, hvc, hvo, hvs, hvk⟩ := exists_subset_iUnion_closure_subset_t2space hS
    (fun i : c => hu i) (fun _ _ => Set.toFinite _) hcover'
  refine ⟨c, v, hvc, hvo, hvk, hvs, ?_⟩
  have hle : (∑ i : c, domainCoefficient K (closure (v i)) f) ≤
      ∑ i : c, domainCoefficient K (u i) f :=
    Finset.sum_le_sum fun i _ => domainCoefficient_mono_of_bdd (hb i) (hvs i)
  apply hle.trans_lt
  rw [Finset.sum_coe_sort c (fun i => domainCoefficient K (u i) f)]
  exact hcost

end LeanShared.DomainPressureRefinement
