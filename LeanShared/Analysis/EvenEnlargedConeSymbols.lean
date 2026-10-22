module
public import LeanShared.Analysis.ConstructedEnlargedConeSymbols
public import LeanShared.Analysis.ProjectionConeTransversality

/-! Even original and enlarged cone cutoffs. For cones symmetric under `ξ ↦ -ξ`, averaging the
original cutoff with its reflection and combining the enlarged cutoffs by `1 - (1-e)(1-e∘(-))`
keeps every support and multiplier condition and makes the original angular symbol even, as
needed for real structure. Projection cones are symmetric. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set
open scoped ContDiff
namespace LeanShared.EvenEnlargedConeSymbols
open ConeDyadicSymbols ConstructedEnlargedConeSymbols

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem projection_cone_neg (P : E →L[ℝ] E) (κ : ℝ) (v : E) :
    -v ∈ ProjectionConeTransversality.cone P κ ↔ v ∈ ProjectionConeTransversality.cone P κ := by
  simp only [ProjectionConeTransversality.cone, mem_ofPred_eq, map_neg, norm_neg]
  rw [show -v - -P v = -(v - P v) by abel, norm_neg]

/-- The reflection-invariant tsupport bound. -/
theorem tsupport_reflect_subset (e : E → ℝ) {C : Set E} (hC : ∀ v, -v ∈ C ↔ v ∈ C)
    (he : tsupport e ⊆ Cᶜ) :
    tsupport (fun ξ => 1 - (1 - e ξ) * (1 - e (-ξ))) ⊆ Cᶜ := by
  have support : Function.support (fun ξ => 1 - (1 - e ξ) * (1 - e (-ξ))) ⊆
      tsupport e ∪ (fun ξ => -ξ) ⁻¹' tsupport e := by
    intro ξ hξ
    by_contra h
    simp only [mem_union, mem_preimage, not_or] at h
    apply hξ
    simp only [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2]
    ring
  have closed : IsClosed (tsupport e ∪ (fun ξ => -ξ) ⁻¹' tsupport e) :=
    (isClosed_tsupport e).union ((isClosed_tsupport e).preimage continuous_neg)
  refine (closure_minimal support closed).trans ?_
  rintro ξ (h | h)
  · exact he h
  · intro hC'
    exact he h ((hC ξ).mpr hC')

/-- The even cutoffs built from arbitrary ones on symmetric cones. -/
def even {Cp Cm : Set E} (c : Cutoffs Cp Cm) (hp : ∀ v, -v ∈ Cp ↔ v ∈ Cp)
    (hm : ∀ v, -v ∈ Cm ↔ v ∈ Cm) : Cutoffs Cp Cm where
  original :=
    { toFun := fun ξ => (c.original.toFun ξ + c.original.toFun (-ξ)) / 2
      smoothAt_unit := fun ξ hξ => by
        have h1 := c.original.smoothAt_unit ξ hξ
        have h2 : ContDiffAt ℝ ∞ (fun ξ => c.original.toFun (-ξ)) ξ :=
          (c.original.smoothAt_unit (-ξ) (by rw [norm_neg]; exact hξ)).comp ξ contDiff_neg.contDiffAt
        exact (h1.add h2).div_const 2
      nonneg_unit := fun ξ hξ => by
        have := c.original.nonneg_unit ξ hξ
        have := c.original.nonneg_unit (-ξ) (by rw [norm_neg]; exact hξ)
        positivity
      le_one_unit := fun ξ hξ => by
        have := c.original.le_one_unit ξ hξ
        have := c.original.le_one_unit (-ξ) (by rw [norm_neg]; exact hξ)
        linarith
      one_on := fun ξ hξ unit => by
        rw [c.original.one_on ξ hξ unit,
          c.original.one_on (-ξ) ((hp ξ).mpr hξ) (by rw [norm_neg]; exact unit)]
        norm_num
      zero_on := fun ξ hξ unit => by
        rw [c.original.zero_on ξ hξ unit,
          c.original.zero_on (-ξ) ((hm ξ).mpr hξ) (by rw [norm_neg]; exact unit)]
        norm_num }
  enlarged := fun s ξ => 1 - (1 - c.enlarged s ξ) * (1 - c.enlarged s (-ξ))
  smooth := fun s => contDiff_const.sub ((contDiff_const.sub (c.smooth s)).mul
    (contDiff_const.sub ((c.smooth s).comp contDiff_neg)))
  plusSupport := tsupport_reflect_subset _ hm c.plusSupport
  minusSupport := tsupport_reflect_subset _ hp c.minusSupport
  one := fun s ξ unit h => by
    have unit' : ‖-ξ‖ = 1 := by rw [norm_neg]; exact unit
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases h1 : 1 - c.original.toFun ξ = 0
      · have h2 : 1 - c.original.toFun (-ξ) ≠ 0 := by
          intro h2
          apply h
          linarith
        have := c.one false (-ξ) unit' (by simpa using h2)
        rw [this]
        ring
      · have := c.one false ξ unit (by simpa using h1)
        rw [this]
        ring
    · simp only [↓reduceIte] at h ⊢
      by_cases h1 : c.original.toFun ξ = 0
      · have h2 : c.original.toFun (-ξ) ≠ 0 := by
          intro h2
          apply h
          rw [h1, h2]
          norm_num
        have := c.one true (-ξ) unit' (by simpa using h2)
        rw [this]
        ring
      · have := c.one true ξ unit (by simpa using h1)
        rw [this]
        ring

theorem even_original {Cp Cm : Set E} (c : Cutoffs Cp Cm) (hp : ∀ v, -v ∈ Cp ↔ v ∈ Cp)
    (hm : ∀ v, -v ∈ Cm ↔ v ∈ Cm) (ξ : E) :
    (even c hp hm).original.toFun (-ξ) = (even c hp hm).original.toFun ξ := by
  change (c.original.toFun (-ξ) + c.original.toFun (- -ξ)) / 2 =
    (c.original.toFun ξ + c.original.toFun (-ξ)) / 2
  rw [neg_neg, add_comm]

end LeanShared.EvenEnlargedConeSymbols
