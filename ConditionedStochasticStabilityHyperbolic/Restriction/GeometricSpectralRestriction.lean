module

public import ConditionedStochasticStabilityHyperbolic.Restriction.GeometricLifting

/-! # Geometric restriction and lifting on nonzero generalized eigenspaces

The restriction map need not be injective on the full continuous space.
Actual kernel extinction makes it injective on every nonzero generalized
eigenspace, and the same geometric threshold supplies its inverse lift.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

section KernelCertificates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {𝕜 : Type*} [RCLike 𝕜]

theorem generalized_restriction_separates
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (U B : Set X) (hU : MeasurableSet U)
    (hreturn : ∀ x : U, ∀ᵐ y ∂C.killedTransition x.val, y ∉ U → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (N : ℕ) (hcomp : ∀ x : ↥(Uᶜ),
      ((LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl) ^ N) x univ = 0)
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hgen : ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0)
    (hRf : restrictObservable U f = 0) : f = 0 := by
  exact generalized_eigenfunction_eq_zero_of_restrict_zero C U B hU
    (ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF) (smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF U hU)
    (ComplexStrongFeller.transferOperator_apply C hSF)
    (smoothedSubtypeTransfer_represents C hSF U hU) hext hreturn
    (smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF Uᶜ hU.compl)
    (smoothedSubtypeTransfer_represents C hSF Uᶜ hU.compl) N
    (smoothedSubtypeTransfer_nilpotent_of_kernel_extinction C hSF Uᶜ hU.compl N hcomp)
    hz k f hgen hRf

end KernelCertificates

section Geometry

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]

theorem exists_geometric_restriction_and_lifting
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
      ∀ (hSF : HasStrongFellerKernel C) (z : 𝕜), z ≠ 0 →
        (∀ (k : ℕ) (f : K →ᵇ 𝕜),
          ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0 →
          restrictObservable V f = 0 → f = 0) ∧
        (∀ (k : ℕ) (g : V →ᵇ 𝕜),
          ((smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF V hV - z • 1) ^ k) g = 0 →
          ∃ f : K →ᵇ 𝕜, restrictObservable V f = g ∧
            ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0) := by
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
  intro hSF z hz
  constructor
  · exact fun k f hf hRf => generalized_restriction_separates _ hSF _
      (badRegion K S) (isClosed_closure.measurableSet.preimage measurable_subtype_coe)
      hreturn hext N hcomp hz k f hf hRf
  · exact fun k g hg => exists_strongFeller_lift_of_complement_extinction _ hSF _ _
      (badRegion K S) hreturn hext N hcomp hz k g hg

end Geometry

end ConditionedStochasticStabilityHyperbolic.Restriction
