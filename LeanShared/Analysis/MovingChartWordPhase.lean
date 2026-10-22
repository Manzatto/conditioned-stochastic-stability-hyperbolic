module

public import LeanShared.Geometry.ActualChartWordFields
public import LeanShared.Analysis.DomainCylinderCoefficient
public import LeanShared.Analysis.RobustFrequencySeparation

/-! Uniform phase separation for the actual endpoint chart of a whole
manifold word. Derivative continuity is required only on the valid moving
closed fibers, near the reference word. No global Euclidean conjugacy or
semicontinuity of an unidentified microscopic constant is assumed. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.MovingChartWordPhase
open CylinderPrincipalCoefficient
variable {E M Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [TopologicalSpace Ω]
  (out inp : OpenPartialHomeomorph M E) (F : Ω → M ≃ₜ M)

/-- Actual differential of the endpoint-chart map of the literal word. -/
def derivative (N : ℕ) (z : (Fin N → Ω) × E) : E →L[ℝ] E :=
  fderiv ℝ (ActualChartWordFields.forward out inp F (List.ofFn z.1)) z.2

/-- The same fixed generator neighborhood works for every point of every
valid moving compact fiber. The source continuity is ordinary chart-C¹
continuity of the two literal derivative fields. -/
theorem exists_uniform_phase (N : ℕ) (reference : Ω)
    (K : Set E) (hK : IsCompact K) (R : Set ((Fin N → Ω) × E)) (hR : IsClosed R)
    (U : Set (Fin N → Ω)) (hU : IsOpen U) (hreference : (fun _ => reference) ∈ U)
    (hd : ContinuousOn (derivative out inp F N) ((U ×ˢ univ) ∩ R))
    (hbase : ContinuousOn (fun z : (Fin N → Ω) × E =>
      derivative out inp F N ((fun _ => reference), z.2)) ((U ×ˢ univ) ∩ R))
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ W : Set Ω, IsOpen W ∧ reference ∈ W ∧
      ∀ word : Fin N → Ω, (∀ i, word i ∈ W) → ∀ x ∈ K,
        (word, x) ∈ R → ∀ ξ η : E, ∀ Λ : ℝ, 0 ≤ Λ → ‖η‖ ≤ 2 * Λ →
        σ * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
          (derivative out inp F N ((fun _ => reference), x)) η‖ →
        (σ / 2) * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
          (derivative out inp F N (word, x)) η‖ := by
  let error : (Fin N → Ω) × E → ℝ := fun z =>
    ‖derivative out inp F N z - derivative out inp F N ((fun _ => reference), z.2)‖
  have herror : ContinuousOn error ((U ×ˢ univ) ∩ R) := (hd.sub hbase).norm
  have hcompact (word : Fin N → Ω) (hw : word ∈ U) :
      IsCompact (values K R error word) := by
    apply isCompact_singleton.union
    apply (fiber_isCompact hK hR word).image_of_continuousOn
    exact herror.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => ⟨⟨hw, mem_univ _⟩, hx.2⟩)
  have hvalues : values K R error (fun _ => reference) = {0} := by
    ext y
    constructor
    · rintro (hy | ⟨x, _, rfl⟩)
      · exact hy
      · simp only [error, sub_self, norm_zero, mem_singleton_iff]
    · exact fun hy => Or.inl hy
  have hzero : coefficient K R error (fun _ => reference) = 0 := by
    rw [coefficient, hvalues]
    exact csSup_singleton 0
  have hsmall : {word | coefficient K R error word < σ / 4} ∈ 𝓝 (fun _ => reference) :=
    DomainCylinderCoefficient.upperSemicontinuousAt_coefficient_on_neighborhood
      hK hR U hU (fun _ => reference) hreference herror (σ / 4)
      (by change coefficient K R error (fun _ => reference) < σ / 4
          rw [hzero]
          positivity)
  obtain ⟨W, hW, hrefW, hbox⟩ := RobustTwoNormBlock.exists_open_box_of_mem_nhds
    N reference (U ∩ {word | coefficient K R error word < σ / 4})
    (inter_mem (hU.mem_nhds hreference) hsmall)
  refine ⟨W, hW, hrefW, ?_⟩
  intro word hw x hx hRx ξ η Λ hΛ hη hgap
  have hwU := (hbox word hw).1
  have he : error (word, x) ≤ coefficient K R error word :=
    le_csSup (hcompact word hwU).bddAbove
      (Or.inr (mem_image_of_mem _ (show x ∈ fiber K R word from ⟨hx, hRx⟩)))
  exact RobustFrequencySeparation.phase_separation_of_derivative_bound _ _ ξ η
    (σ / 4) 2 σ Λ (by positivity) hΛ
    (he.trans (hbox word hw).2.le) hη hgap (by linarith)

end LeanShared.MovingChartWordPhase
