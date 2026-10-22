module

public import LeanShared.Geometry.ActualChartWordFields
public import LeanShared.Analysis.DomainCylinderCoefficient

/-! Genuine moving chart-pair fibers. Compact source and target cutoff
supports determine the relation. Its closedness and a common neighborhood
on which reference chart inverses remain valid are derived from actual
word continuity and compactness. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.ActualChartWordFibers
variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace Ω]
  (out inp : OpenPartialHomeomorph M E) (F : Ω → M ≃ₜ M)

/-- Both fixed cutoffs have their actual supports in their genuine charts. -/
def relation (N : ℕ) (K : Set E) (targetSupport : Set M) : Set ((Fin N → Ω) × E) :=
  (univ ×ˢ K) ∩ (fun z => ActualFiniteRegularWord.orbit (fun a => F a)
    (List.ofFn z.1) (out.symm z.2)) ⁻¹' targetSupport

include inp in
/-- Current and reference word fields need only be differentiated where
the actual endpoint lies in the incoming chart. -/
def valid (N : ℕ) : Set ((Fin N → Ω) × E) :=
  {z | z.2 ∈ out.target ∧ ActualFiniteRegularWord.orbit (fun a => F a)
    (List.ofFn z.1) (out.symm z.2) ∈ inp.source}

omit [NormedSpace ℝ E] in
theorem relation_closed (N : ℕ) {K : Set E} (hK : IsClosed K) (hKt : K ⊆ out.target)
    {targetSupport : Set M} (hS : IsClosed targetSupport)
    (hF : Continuous (fun z : Ω × M => F z.1 z.2)) :
    IsClosed (relation out F N K targetSupport) := by
  have hs : ContinuousOn (fun z : (Fin N → Ω) × E => out.symm z.2) (univ ×ˢ K) :=
    out.symm.continuousOn.comp continuous_snd.continuousOn (fun _ hz => hKt hz.2)
  have he : ContinuousOn (fun z : (Fin N → Ω) × E =>
      ActualFiniteRegularWord.orbit (fun a => F a) (List.ofFn z.1) (out.symm z.2)) (univ ×ˢ K) :=
    (ActualFiniteRegularWord.continuous_orbit_ofFn (fun a => F a) hF N).comp_continuousOn
      (continuous_fst.continuousOn.prodMk hs)
  exact he.preimage_isClosed_of_isClosed (isClosed_univ.prod hK) hS

omit [NormedSpace ℝ E] [TopologicalSpace Ω] in
theorem relation_subset_valid (N : ℕ) {K : Set E} (hKt : K ⊆ out.target)
    {targetSupport : Set M} (hSt : targetSupport ⊆ inp.source) :
    relation out F N K targetSupport ⊆ valid out inp F N :=
  fun _ hz => ⟨hKt hz.1.2, hSt hz.2⟩

omit [NormedSpace ℝ E] in
theorem exists_reference_valid_neighborhood (N : ℕ) (reference : Ω)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ out.target)
    {targetSupport : Set M} (hS : IsClosed targetSupport) (hSt : targetSupport ⊆ inp.source)
    (hF : Continuous (fun z : Ω × M => F z.1 z.2)) :
    ∃ U : Set (Fin N → Ω), IsOpen U ∧ (fun _ => reference) ∈ U ∧
      ∀ word ∈ U, ∀ x ∈ K, (word, x) ∈ relation out F N K targetSupport →
        x ∈ ActualChartWordFields.domain out inp F (List.ofFn (fun _ : Fin N => reference)) := by
  let R := relation out F N K targetSupport
  let O := ActualChartWordFields.domain out inp F (List.ofFn (fun _ : Fin N => reference))
  have hR : IsClosed R := relation_closed out F N hK.isClosed hKt hS hF
  have hO : IsOpen O := ActualChartWordFields.domain_open out inp F _
  have hsub : ({fun _ : Fin N => reference} : Set (Fin N → Ω)) ×ˢ K ⊆
      Rᶜ ∪ (univ ×ˢ O) := by
    rintro ⟨word, x⟩ ⟨hw, hx⟩
    have hw' : word = fun _ => reference := mem_singleton_iff.mp hw
    subst word
    by_cases hr : ((fun _ => reference), x) ∈ R
    · exact Or.inr ⟨mem_univ _, hKt hx, hSt hr.2⟩
    · exact Or.inl hr
  obtain ⟨U, W, hU, _, href, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton hK (hR.isOpen_compl.union (isOpen_univ.prod hO)) hsub
  refine ⟨U, hU, singleton_subset_iff.mp href, ?_⟩
  intro word hw x hx hr
  exact (hUW ⟨hw, hKW hx⟩).resolve_left (not_not.mpr hr) |>.2

end LeanShared.ActualChartWordFibers
