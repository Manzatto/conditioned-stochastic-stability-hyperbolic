module

public import ConditionedStochasticStabilityHyperbolic.Restriction.FiniteLifting
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.Perturbations

/-!
# Geometric noise certificates on the literal live-state type

Finite pseudo-orbit exit is transferred to actual subtype paths, without
assuming that the deterministic map preserves the live region. The final
lifting bridge uses the full live type `K`, and a further measurable subtype
for the retained neighborhood.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

section EmbeddedPaths

variable {Y Z : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- An actual live-state path can be tested in an ambient geometric space.
There is no requirement that the ambient deterministic map preserve the live type. -/
theorem finite_extinction_of_embedded_exit
    (D : AbsorbingMarkovChains.CanonicalChain Y) (ι : Y → Z) (hι : Measurable ι)
    (T : Z ≃ₜ Z) (B : Set Y) (N : ℕ) (δ : ℝ)
    (hsupport : ∀ y, ∀ᵐ z ∂D.killedTransition y, dist (ι z) (T (ι y)) < δ)
    (hexit : ∀ z : ℕ → Y, z 0 ∈ B →
      (∀ j < N, dist (ι (z (j + 1))) (T (ι (z j))) < δ) → False) :
    ∀ y ∈ B, D.pathMeasure y (AbsorbingMarkovChains.CanonicalChain.survival N) = 0 := by
  have hrel : MeasurableSet {p : Y × Y | dist (ι p.2) (T (ι p.1)) < δ} :=
    measurableSet_lt ((hι.comp measurable_snd).dist
      (T.continuous.measurable.comp (hι.comp measurable_fst))) measurable_const
  intro y hy
  have hsteps : ∀ᵐ ω ∂D.pathMeasure y, ∀ n, ∀ u v,
      ω n = some u → ω (n + 1) = some v → dist (ι v) (T (ι u)) < δ :=
    ae_all_iff.2 (fun n => ae_live_transition_relation D _ hrel hsupport y n)
  have hn : ∀ᵐ ω ∂D.pathMeasure y,
      ω ∉ AbsorbingMarkovChains.CanonicalChain.survival N := by
    filter_upwards [hsteps, ae_path_initial_state D y] with ω hω hinit
    intro hs
    let z : ℕ → Y := fun j => (ω j).getD y
    have hsome (j : ℕ) (hj : j ≤ N) : ω j = some (z j) := by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hs j hj)
      simp [z, hv]
    have hz0 : z 0 = y := by simp [z, hinit]
    apply hexit z (hz0.symm ▸ hy)
    intro j hj
    exact hω j (z j) (z (j + 1)) (hsome j (by omega)) (hsome (j + 1) (by omega))
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

end EmbeddedPaths

section RestrictedNoiseSupport

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Random-map support pulls back to the literal weighted live-state chain,
with the departure weight defined only on that live type. -/
theorem restricted_noise_chain_support
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (w : K → ℝ) (hw : Measurable w)
    (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (R : X × X → Prop) (hR : MeasurableSet {p | R p})
    (himages : ∀ x ∈ K, ∀ ω, F (x, ω) ∈ K → R (x, F (x, ω))) :
    ∀ x : K, ∀ᵐ y ∂(RestrictedNoise.chain ρ F hF K hK w hw W hW hwW).killedTransition x,
      R (x.val, y.val) := by
  let wa := LeanShared.SubtypeKernel.zeroExtend K w
  have hwa : Measurable wa := LeanShared.SubtypeKernel.measurable_zeroExtend K hK w hw
  have hwaW : ∀ x, wa x ≤ W := LeanShared.SubtypeKernel.zeroExtend_le K w W hW.le hwW
  have hc := RestrictedNoise.killedTransition_eq_restrict ρ F hF K hK w hw W hW hwW
    wa hwa hwaW (LeanShared.SubtypeKernel.zeroExtend_coe K w)
  intro x
  rw [hc]
  have hsource : ∀ᵐ y ∂(NoiseKernel.chain ρ F hF K hK wa hwa W hW hwaW).killedTransition x.val,
      R (x.val, y) := by
    have hR' : MeasurableSet {p : X × X | p.1 ∈ K → R p} :=
      MeasurableSet.imp (hK.preimage measurable_fst) hR
    have h := noise_chain_support ρ F hF K hK wa hwa W hW hwaW
      (fun p => p.1 ∈ K → R p) hR' (fun u ω hdest hu => himages u hu ω hdest) x.val
    filter_upwards [h] with y hy
    exact hy x.property
  exact (ae_restrict_iff_subtype hK).1 (ae_restrict_of_ae hsource)

end RestrictedNoiseSupport

section GeometricCertificates

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]

/-- The paper's retained closed neighborhood inside the full live type. -/
def retainedRegion (K U : Set X) : Set K := Subtype.val ⁻¹' closure U

/-- The exterior of the stable neighborhood, inside the actual full live type. -/
def badRegion (K S : Set X) : Set K := Subtype.val ⁻¹' Sᶜ

/-- The literal subtype chain for a sub-Markov killed kernel. -/
def subtypeChain {Y : Type*} [MeasurableSpace Y]
    (C : AbsorbingMarkovChains.CanonicalChain Y) (V : Set Y) (hV : MeasurableSet V) :
    AbsorbingMarkovChains.CanonicalChain V :=
  WeightedKernel.ofSubMarkov (LeanShared.SubtypeKernel.restrict C.killedTransition V hV)
    (LeanShared.SubtypeKernel.restrict_mass_le_one C.killedTransition V hV
      C.killedTransition_mass_le_one)

@[simp]
theorem subtypeChain_killedTransition {Y : Type*} [MeasurableSpace Y]
    (C : AbsorbingMarkovChains.CanonicalChain Y) (V : Set Y) (hV : MeasurableSet V) :
    (subtypeChain C V hV).killedTransition =
      LeanShared.SubtypeKernel.restrict C.killedTransition V hV :=
  WeightedKernel.ofSubMarkov_killedTransition _ _

/-- Existing robust finite exit and noise nonreturn supply both actual
kernel certificates needed by continuous spectral lifting, on the exact
nested live types `K` and `K ∩ closure U`. -/
theorem exists_geometric_lifting_certificates
    (T : X ≃ₜ X) (K U S : Set X) (hK : IsCompact K) (hU : IsOpen U) (hS : IsOpen S)
    (hcore : LeanShared.isolatedCore T K ⊆ U)
    (hstable : LeanShared.forwardTrapped T K ⊆ S)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧
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
  intro F hF hclose hnonreturn
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

/-- The deterministic neighborhood separation already proved in `Neighborhoods.Basic` supplies noise
nonreturn. Together with the finite-exit geometry, it gives actual continuous spectral lifting
for every sufficiently close noisy map, on the manuscript's closed retained neighborhood. -/
theorem exists_geometric_generalized_lifting
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ LeanShared.forwardTrapped T K ⊆ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    {𝕜 : Type*} [RCLike 𝕜] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
      let V := retainedRegion K U
      let hV : MeasurableSet V := isClosed_closure.measurableSet.preimage measurable_subtype_coe
      ∀ (hSF : HasStrongFellerKernel C) (z : 𝕜), z ≠ 0 → ∀ (k : ℕ) (g : V →ᵇ 𝕜),
        ((smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF V hV - z • 1) ^ k) g = 0 →
        ∃ f : K →ᵇ 𝕜, restrictObservable V f = g ∧
          ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0 := by
  obtain ⟨r, hr, hnonreturn⟩ := LeanShared.exists_uniform_nonreturn T.continuous
    isClosed_closure.isCompact (LeanShared.isClosed_forwardTrapped T.continuous hK.isClosed)
    hU hsep
  let S := Metric.thickening r (LeanShared.forwardTrapped T K)
  have hS : IsOpen S := Metric.isOpen_thickening
  have hstable : LeanShared.forwardTrapped T K ⊆ S := Metric.self_subset_thickening hr _
  obtain ⟨N, _hN, δ, hδ, hcert⟩ := exists_geometric_lifting_certificates
    T K U S hK hU hS hcore hstable ρ w hw W hW hwW
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro F hF hclose
  have hcloseδ : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ :=
    fun x hx ω => (hclose x hx ω).trans_le (min_le_left _ _)
  have hnoise_nonreturn : ∀ x ∈ K, x ∈ closure U → ∀ ω, F (x, ω) ∉ S \ U := by
    intro x _hx hxU ω
    exact hnonreturn (fun y => F (y, ω))
      (fun y hy => (hclose y (hUK hy) ω).trans_le (min_le_right _ _)) x hxU
  obtain ⟨hreturn, hext, hcomp⟩ := hcert F hF hcloseδ hnoise_nonreturn
  dsimp only
  intro hSF z hz k g hg
  exact exists_strongFeller_lift_of_complement_extinction _ hSF _ _
    (badRegion K S) hreturn hext N hcomp hz k g hg

end GeometricCertificates

end ConditionedStochasticStabilityHyperbolic.Restriction
