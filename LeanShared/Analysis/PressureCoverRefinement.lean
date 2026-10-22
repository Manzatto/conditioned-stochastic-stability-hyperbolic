module

public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking pressure covers without increasing their coefficient

The pressure coefficient in Baladi--Tsujii (2008), §3 (3.2), is a minimum
over finite open cylinder covers. Its scalar pressure asymptotic does not
apply to an arbitrarily selected family of closed cylinders. A selected
open cover can instead be shrunk, keeping the same index set, to compact
outer sets with an open inner cover. Their coefficients do not increase.
This gives the robust cover required by the moving-cylinder argument
without asserting a new asymptotic for the refined family.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace LeanShared.PressureCoverRefinement

variable {X I : Type*} [TopologicalSpace X]

/-- Zero is included so that empty members of a pressure cover cost zero. -/
def domainCoefficient (K A : Set X) (f : X → ℝ) : ℝ :=
  sSup ({0} ∪ f '' (K ∩ A))

theorem domainValues_bddAbove {K A : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : Continuous f) :
    BddAbove ({0} ∪ f '' (K ∩ A)) :=
  (isCompact_singleton.union (hK.image hf)).bddAbove.mono
    (union_subset_union_right _ (image_mono inter_subset_left))

theorem domainCoefficient_mono {K A B : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : Continuous f) (hAB : A ⊆ B) :
    domainCoefficient K A f ≤ domainCoefficient K B f := by
  unfold domainCoefficient
  exact csSup_le_csSup (domainValues_bddAbove hK hf)
    (show ({0} ∪ f '' (K ∩ A) : Set ℝ).Nonempty from
      ⟨0, Or.inl (mem_singleton 0)⟩)
    (union_subset_union_right _ (image_mono (inter_subset_inter_right K hAB)))

theorem domainCoefficient_nonneg {K A : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : Continuous f) : 0 ≤ domainCoefficient K A f :=
  le_csSup (domainValues_bddAbove hK hf) (Or.inl (mem_singleton 0))

/-- The source coefficient is the infimum over finite selected open
cylinder subcovers. Existence of a minimizer is not needed. -/
def coverCoefficient (K S : Set X) (u : I → Set X) (f : X → ℝ) : ℝ :=
  sInf {a | ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
    a = ∑ i ∈ c, domainCoefficient K (u i) f}

omit [TopologicalSpace X] in
theorem exists_cover_cost_lt {K S : Set X} {u : I → Set X} {f : X → ℝ} {a : ℝ}
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i)
    (hstrict : coverCoefficient K S u f < a) :
    ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
      (∑ i ∈ c, domainCoefficient K (u i) f) < a := by
  obtain ⟨c, hc⟩ := hcover
  have hne : ({b | ∃ d : Finset I, S ⊆ ⋃ i ∈ d, u i ∧
      b = ∑ i ∈ d, domainCoefficient K (u i) f} : Set ℝ).Nonempty :=
    ⟨_, c, hc, rfl⟩
  obtain ⟨b, ⟨d, hd, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hne hstrict
  exact ⟨d, hd, hb⟩

theorem coverCoefficient_nonneg {K S : Set X} {u : I → Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : Continuous f)
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i) :
    0 ≤ coverCoefficient K S u f := by
  obtain ⟨c, hc⟩ := hcover
  apply le_csInf (s := {b | ∃ d : Finset I, S ⊆ ⋃ i ∈ d, u i ∧
    b = ∑ i ∈ d, domainCoefficient K (u i) f})
    (show ({b | ∃ d : Finset I, S ⊆ ⋃ i ∈ d, u i ∧
      b = ∑ i ∈ d, domainCoefficient K (u i) f} : Set ℝ).Nonempty from ⟨_, c, hc, rfl⟩)
  rintro b ⟨d, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => domainCoefficient_nonneg hK hf

variable [T2Space X] [LocallyCompactSpace X] [Fintype I]

/-- A pressure cover is shrunk without duplication or a multiplicity
factor. The inner opens cover the surviving compact set; the outer
closures stay in the original cylinders and have smaller coefficients. -/
theorem exists_shrinking_coefficient_le {K S : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hS : IsCompact S) (hf : Continuous f)
    (u : I → Set X) (hu : ∀ i, IsOpen (u i)) (hcover : S ⊆ ⋃ i, u i) :
    ∃ v : I → Set X,
      S ⊆ ⋃ i, v i ∧ (∀ i, IsOpen (v i)) ∧
      (∀ i, IsCompact (closure (v i))) ∧
      (∀ i, closure (v i) ⊆ u i) ∧
      (∑ i, domainCoefficient K (closure (v i)) f) ≤
        ∑ i, domainCoefficient K (u i) f := by
  obtain ⟨v, hvcover, hvopen, hvsub, hvcompact⟩ :=
    exists_subset_iUnion_closure_subset_t2space hS hu
      (fun _ _ => Set.toFinite _) hcover
  refine ⟨v, hvcover, hvopen, hvcompact, hvsub, ?_⟩
  exact Finset.sum_le_sum fun i _ => domainCoefficient_mono hK hf (hvsub i)

/-- Strictness of the selected source coefficient survives refinement.
There is no extra exponential or cover-cardinality loss. -/
theorem exists_shrinking_strict {K S : Set X} {f : X → ℝ} {a : ℝ}
    (hK : IsCompact K) (hS : IsCompact S) (hf : Continuous f)
    (u : I → Set X) (hu : ∀ i, IsOpen (u i)) (hcover : S ⊆ ⋃ i, u i)
    (hstrict : (∑ i, domainCoefficient K (u i) f) < a) :
    ∃ v : I → Set X,
      S ⊆ ⋃ i, v i ∧ (∀ i, IsOpen (v i)) ∧
      (∀ i, IsCompact (closure (v i))) ∧
      (∀ i, closure (v i) ⊆ u i) ∧
      (∑ i, domainCoefficient K (closure (v i)) f) < a := by
  obtain ⟨v, hvc, hvo, hvk, hvs, hsum⟩ :=
    exists_shrinking_coefficient_le hK hS hf u hu hcover
  exact ⟨v, hvc, hvo, hvk, hvs, hsum.trans_lt hstrict⟩

omit [Fintype I] in
/-- Select a source pressure subcover and construct the closed/open
refinement directly from strictness of the infimum coefficient. Thus no
root asymptotic for a preselected closed cover is an input. -/
theorem exists_refined_pressure_cover {K S : Set X} {f : X → ℝ} {a : ℝ}
    (hK : IsCompact K) (hS : IsCompact S) (hf : Continuous f)
    (u : I → Set X) (hu : ∀ i, IsOpen (u i))
    (hcover : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i)
    (hstrict : coverCoefficient K S u f < a) :
    ∃ (c : Finset I) (v : c → Set X),
      S ⊆ ⋃ i, v i ∧ (∀ i, IsOpen (v i)) ∧
      (∀ i, IsCompact (closure (v i))) ∧
      (∀ i, closure (v i) ⊆ u i) ∧
      (∑ i, domainCoefficient K (closure (v i)) f) < a := by
  classical
  obtain ⟨c, hc, hcost⟩ := exists_cover_cost_lt hcover hstrict
  have hcover' : S ⊆ ⋃ i : c, u i := by
    intro x hx
    obtain ⟨i, hic, hxi⟩ := mem_iUnion₂.mp (hc hx)
    exact mem_iUnion.mpr ⟨⟨i, hic⟩, hxi⟩
  have hcost' : (∑ i : c, domainCoefficient K (u i) f) < a := by
    rw [Finset.sum_coe_sort c (fun i => domainCoefficient K (u i) f)]
    exact hcost
  obtain ⟨v, hvc, hvo, hvk, hvs, hvsum⟩ :=
    exists_shrinking_strict hK hS hf (fun i : c => u i)
      (fun i => hu i) hcover' hcost'
  exact ⟨c, v, hvc, hvo, hvk, hvs, hvsum⟩

end LeanShared.PressureCoverRefinement
