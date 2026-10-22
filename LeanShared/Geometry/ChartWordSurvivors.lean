module

public import LeanShared.Geometry.ActualChartWordFibers
public import LeanShared.Dynamics.FiniteWordCylinders

/-! Actual closed word supports include every chronological prefix.
Endpoint membership alone does not give the cone-hyperbolicity domain of
an accumulated cutoff weight. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.ChartWordSurvivors
open CylinderPrincipalCoefficient
variable {E M Ω J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace Ω]

/-- Closed manifold cylinder formed by the actual partition supports. -/
def supportCylinder (F : Ω → M → M) (cutoff : J → M → ℂ) (N : ℕ)
    (labels : Fin (N + 1) → J) : Set ((Fin N → Ω) × M) :=
  {z | ∀ j : Fin (N + 1), prefixOrbit F z.1 j.val z.2 ∈ tsupport (cutoff (labels j))}

theorem supportCylinder_closed (F : Ω → M → M) (cutoff : J → M → ℂ)
    (hF : Continuous (fun z : Ω × M => F z.1 z.2)) (N : ℕ)
    (labels : Fin (N + 1) → J) : IsClosed (supportCylinder F cutoff N labels) := by
  have heq : supportCylinder F cutoff N labels = ⋂ j : Fin (N + 1),
      (fun z : (Fin N → Ω) × M => prefixOrbit F z.1 j.val z.2) ⁻¹' tsupport (cutoff (labels j)) := by
    ext z
    simp only [supportCylinder, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isClosed_iInter fun j => (isClosed_tsupport _).preimage (continuous_prefixOrbit F hF N j.val)

/-- Genuine coordinate support of a whole word: initial compact chart
support, all live prefixes, and all partition-cutoff itinerary supports. -/
def relation (out : OpenPartialHomeomorph M E) (F : Ω → M → M)
    (cutoff : J → M → ℂ) (live : Set M) (N : ℕ)
    (labels : Fin (N + 1) → J) (K : Set E) : Set ((Fin N → Ω) × E) :=
  (univ ×ˢ K) ∩ (fun z => (z.1, out.symm z.2)) ⁻¹'
    (FiniteWordCylinders.survivors F live N ∩ supportCylinder F cutoff N labels)

omit [NormedSpace ℝ E] in
theorem relation_closed (out : OpenPartialHomeomorph M E) (F : Ω → M → M)
    (cutoff : J → M → ℂ) {live : Set M} (hlive : IsClosed live)
    (hF : Continuous (fun z : Ω × M => F z.1 z.2)) (N : ℕ)
    (labels : Fin (N + 1) → J) {K : Set E} (hK : IsClosed K) (hKt : K ⊆ out.target) :
    IsClosed (relation out F cutoff live N labels K) := by
  have hs : ContinuousOn (fun z : (Fin N → Ω) × E => out.symm z.2) (univ ×ˢ K) :=
    out.symm.continuousOn.comp continuous_snd.continuousOn (fun _ hz => hKt hz.2)
  exact (continuous_fst.continuousOn.prodMk hs).preimage_isClosed_of_isClosed
    (isClosed_univ.prod hK)
    ((FiniteWordCylinders.survivors_closed F hF live hlive N).inter
      (supportCylinder_closed F cutoff hF N labels))

omit [TopologicalSpace Ω] [NormedSpace ℝ E] in
theorem relation_subset_valid (out inp : OpenPartialHomeomorph M E) (F : Ω → M ≃ₜ M)
    (cutoff : J → M → ℂ) (live : Set M) (N : ℕ) (labels : Fin (N + 1) → J)
    {K : Set E} (hKt : K ⊆ out.target)
    (hfinal : tsupport (cutoff (labels (Fin.last N))) ⊆ inp.source) :
    relation out (fun a => F a) cutoff live N labels K ⊆ ActualChartWordFibers.valid out inp F N := by
  intro z hz
  refine ⟨hKt hz.1.2, hfinal ?_⟩
  have h := hz.2.2 (Fin.last N)
  simpa only [ActualFiniteRegularWord.orbit_ofFn_eq_prefix, Fin.val_last] using h

end LeanShared.ChartWordSurvivors
