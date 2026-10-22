module

public import LeanShared.Geometry.SupportedRegularPairing

/-! A faithful ordinary distribution embedding proves that the constructed
analytic space is nontrivial, using a literal supported smooth bump. No
separation property of an arbitrary family of leaves is presumed. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology BoundedContinuousFunction
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M Reg B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  {V K : Set M} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace K] [BorelSpace K] in
theorem physicalCore_tsupport (c : core (E := E) V) :
    tsupport (physicalCore V K c) ⊆ {x : K | x.val ∈ V} := by
  have hs : tsupport (physicalCore V K c) ⊆
      (Subtype.val : K → M) ⁻¹' tsupport (functions V c) := by
    apply closure_minimal ?_ ((isClosed_tsupport _).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport (functions V c) hx
  exact fun x hx => support V c (hs hx)

/-- The common smooth integral identity and reference positivity produce an
actual nonzero analytic vector. Neither nontriviality nor a separating leaf
family is a hidden topological-dynamics assumption. -/
theorem nontrivial_of_common_distribution_pairing
    (hK : IsClosed K) (hV : IsOpen V) (x : K) (hx : x.val ∈ V)
    (σ : Measure K) [IsFiniteMeasure σ]
    (q : core (E := E) V →ₗ[ℂ] Reg)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ))
    (hphysical : ∀ c, physical (q c) = physicalCore V K c)
    (hpositive : {y : K | y.val ∈ V} ⊆ σ.support)
    (qa : core (E := E) V →ₗ[ℂ] B) (a : B →L[ℂ] (Reg →L[ℂ] ℂ))
    (hcommon : ∀ c, a (qa c) = SupportedRegularPairing.embedding σ physical (physicalCore V K c)) :
    Nontrivial B := by
  obtain ⟨ζ, hζ, _, hζsupp, hζone⟩ :=
    SmoothWeightCutoff.exists_cutoff (E := E) {x.val} V (isCompact_singleton)
      hV (singleton_subset_iff.mpr hx)
  let c : core (E := E) V := ⟨fun y => (ζ y : ℂ),
    Complex.ofRealCLM.contMDiff.comp hζ, by
      apply (closure_mono ?_).trans hζsupp
      intro y hy
      exact fun hz => hy (by simp [hz])⟩
  have hc : physicalCore V K c ≠ 0 := by
    intro h
    have hv := congrArg (fun f : K →ᵇ ℂ => f x) h
    change (ζ x.val : ℂ) = 0 at hv
    rw [hζone x.val (mem_singleton _)] at hv
    exact one_ne_zero hv
  have hqa : qa c ≠ 0 := by
    intro h
    apply hc
    apply physical_pairing_faithful hK hV σ q physical hphysical hpositive
      (physicalCore V K c) (physicalCore_tsupport c)
    rw [← hcommon, h, map_zero]
  exact ⟨⟨qa c, 0, hqa⟩⟩

end LeanShared.SmoothSupportedManifoldCore
