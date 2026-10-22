module

public import ConditionedStochasticStabilityHyperbolic.Restriction.NoiseDoobLocalization

/-! Law-independent geometric noise thresholds. The finite orbit estimates
are chosen before any driving measure or departure weight. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.UniformNoiseLocalization
open Restriction LeanShared

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]

theorem exists_uniform_geometric_lifting_certificates
    (T : X ≃ₜ X) (K U S : Set X) (hK : IsCompact K) (hU : IsOpen U) (hS : IsOpen S)
    (hcore : LeanShared.isolatedCore T K ⊆ U)
    (hstable : LeanShared.forwardTrapped T K ⊆ S) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W),
      ∀ (F : X × Ω → X) (hF : Measurable F),
        (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
        (∀ x ∈ K, x ∈ closure U → ∀ ω, F (x, ω) ∉ S \ U) →
        let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
        let V := retainedRegion K U
        let hV : MeasurableSet V := isClosed_closure.measurableSet.preimage measurable_subtype_coe
        (∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ badRegion K S) ∧
        (∀ x ∈ badRegion K S, ∃ n : ℕ,
          C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0) ∧
        (∀ x : ↥(Vᶜ), ((LeanShared.SubtypeKernel.restrict C.killedTransition Vᶜ hV.compl) ^ N)
          x univ = 0) := by
  have hB : IsCompact (K \ S) := hK.diff hS
  have hdis : Disjoint (K \ S) (LeanShared.forwardTrapped T K) := by
    rw [Set.disjoint_left]
    intro x hx hs
    exact hx.2 (hstable hs)
  obtain ⟨Nb, _hNb, δb, hδb, hexitb⟩ := LeanShared.exists_pos_robust_forward_exit
    (CompactSpace.uniformContinuous_of_continuous T.continuous) hK.isClosed hB hdis
  obtain ⟨N, hN, δc, hδc, hexitc⟩ := LeanShared.exists_pos_robust_entrance_or_exit T
    (CompactSpace.uniformContinuous_of_continuous T.continuous) hK hU hcore
  refine ⟨N, hN, min δb δc, lt_min hδb hδc, ?_⟩
  intro ρ _ w hw W hW hwW F hF hclose hnonreturn
  let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
  let V := retainedRegion K U
  have hV : MeasurableSet V := isClosed_closure.measurableSet.preimage measurable_subtype_coe
  have hstep : ∀ x : K, ∀ᵐ y ∂C.killedTransition x,
      dist y.val (T x.val) < min δb δc := by
    apply restricted_noise_chain_support ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
      (fun p => dist p.2 (T p.1) < min δb δc)
      (measurableSet_lt (measurable_snd.dist (T.continuous.measurable.comp measurable_fst))
        measurable_const)
    exact fun x hx ω _ => hclose x hx ω
  refine ⟨?_, ?_, ?_⟩
  · have hR : MeasurableSet {p : X × X | p.1 ∈ closure U →
        p.2 ∉ closure U → p.2 ∉ S} :=
      MeasurableSet.imp (isClosed_closure.measurableSet.preimage measurable_fst)
        (MeasurableSet.imp ((isClosed_closure.measurableSet.preimage measurable_snd).compl)
          ((hS.measurableSet.preimage measurable_snd).compl))
    have h := restricted_noise_chain_support ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
      (fun p => p.1 ∈ closure U → p.2 ∉ closure U → p.2 ∉ S) hR
      (fun x hx ω _ hxu hy hys =>
        hnonreturn x hx hxu ω ⟨hys, fun hyU => hy (subset_closure hyU)⟩)
    intro x
    filter_upwards [h x.val] with y hy hout
    exact hy x.property hout
  · have hbadext : ∀ x ∈ badRegion K S,
        C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival Nb) = 0 := by
      apply finite_extinction_of_embedded_exit C Subtype.val measurable_subtype_coe
        T (badRegion K S) Nb δb
      · intro x
        filter_upwards [hstep x] with y hy
        exact hy.trans_le (min_le_left _ _)
      · intro z hz hnear
        obtain ⟨j, _hj, hbad⟩ := hexitb (fun j => (z j).val)
          ⟨(z 0).property, hz⟩ (fun j hj _ => hnear j hj)
        exact hbad (z j).property
    exact fun x hx => ⟨Nb, hbadext x hx⟩
  · let D := subtypeChain C Vᶜ hV.compl
    have hDstep : ∀ x : ↥(Vᶜ), ∀ᵐ y ∂D.killedTransition x,
        dist y.val.val (T x.val.val) < δc := by
      intro x
      rw [subtypeChain_killedTransition]
      have ha : ∀ᵐ y ∂C.killedTransition x.val, dist y.val (T x.val.val) < δc := by
        filter_upwards [hstep x.val] with y hy
        exact hy.trans_le (min_le_right _ _)
      exact (ae_restrict_iff_subtype hV.compl).1 (ae_restrict_of_ae ha)
    have hDext := finite_extinction_of_embedded_exit D
      (fun x : ↥(Vᶜ) => x.val.val) (measurable_subtype_coe.comp measurable_subtype_coe)
      T univ N δc hDstep (by
        intro z _hz hnear
        have hnot (j : ℕ) : (z j).val.val ∉ U := by
          intro hj
          exact (z j).property (subset_closure hj)
        obtain ⟨j, _hj, hbad⟩ := hexitc (fun j => (z j).val.val)
          ⟨(z 0).val.property, hnot 0⟩ (fun j hj _ => hnear j hj)
        exact hbad.elim (fun h => h (z j).val.property) (hnot j))
    intro x
    have hx := hDext x (mem_univ x)
    rw [D.pathMeasure_survival, subtypeChain_killedTransition] at hx
    exact hx

theorem exists_uniform_noise_eigenvectorMeasure_localization
    (T : X ≃ₜ X) (K U O : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ LeanShared.forwardTrapped T K ⊆ U)
    (hUO : closure U ⊆ O)
:
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W),
      ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
      ∀ (g : K →ᵇ ℝ), (∀ x, 0 ≤ g x) → ∀ (r : ℝ), 0 < r →
      (∀ x, ∫ y, g y ∂C.killedTransition x = r * g x) →
      ∀ (μ : Measure K), C.killedTransition ∘ₘ μ = ENNReal.ofReal r • μ →
        LeanShared.eigenvectorMeasure μ g (retainedRegion K U)ᶜ = 0 ∧
        (LeanShared.eigenvectorMeasure μ g).support ⊆ retainedRegion K U ∧
        ((LeanShared.eigenvectorMeasure μ g).map Subtype.val).support ⊆ closure U ∧
        ((LeanShared.eigenvectorMeasure μ g).map Subtype.val).support ⊆ O := by
  obtain ⟨r₀, hr₀, hnonreturn⟩ := LeanShared.exists_uniform_nonreturn T.continuous
    isClosed_closure.isCompact (LeanShared.isClosed_forwardTrapped T.continuous hK.isClosed)
    hU hsep
  let S := Metric.thickening r₀ (LeanShared.forwardTrapped T K)
  obtain ⟨N, _hN, δ, hδ, hcert⟩ := exists_uniform_geometric_lifting_certificates
    (Ω := Ω) T K U S hK hU Metric.isOpen_thickening hcore
      (Metric.self_subset_thickening hr₀ _)
  refine ⟨min δ r₀, lt_min hδ hr₀, ?_⟩
  intro ρ _ w hw W hW hwW F hF hclose
  have hcloseδ : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ :=
    fun x hx ω => (hclose x hx ω).trans_le (min_le_left _ _)
  have hnoise : ∀ x ∈ K, x ∈ closure U → ∀ ω, F (x, ω) ∉ S \ U := by
    intro x _hx hxU ω
    exact hnonreturn (fun y => F (y, ω))
      (fun y hy => (hclose y (hUK hy) ω).trans_le (min_le_right _ _)) x hxU
  obtain ⟨hreturn, hbad, hcomp⟩ := hcert ρ w hw W hW hwW F hF hcloseδ hnoise
  dsimp only
  intro g hg r hr heigen μ hleft
  let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  have hV : IsClosed (retainedRegion K U) := isClosed_closure.preimage continuous_subtype_val
  have hmV : MeasurableSet (retainedRegion K U) := hV.measurableSet
  have hbad' : ∀ x ∈ badRegion K S, ∃ n : ℕ, (C.killedTransition ^ n) x univ = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := hbad x hx
    change C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0 at hn
    exact ⟨n, by rwa [C.pathMeasure_survival] at hn⟩
  obtain ⟨hz, hs⟩ := real_eigenvectorMeasure_localization C.killedTransition g hg r hr heigen
    μ hleft (retainedRegion K U) hV hmV (badRegion K S)
    (fun x hx => hreturn ⟨x, hx⟩) hbad' N hcomp
  have hamb : ((LeanShared.eigenvectorMeasure μ g).map Subtype.val).support ⊆ closure U := by
    apply Measure.support_subset_of_isClosed isClosed_closure
    change ((LeanShared.eigenvectorMeasure μ g).map Subtype.val) (closure U)ᶜ = 0
    rw [Measure.map_apply measurable_subtype_coe isClosed_closure.measurableSet.compl]
    exact hz
  exact ⟨hz, hs, hamb, hamb.trans hUO⟩

end ConditionedStochasticStabilityHyperbolic.UniformNoiseLocalization
