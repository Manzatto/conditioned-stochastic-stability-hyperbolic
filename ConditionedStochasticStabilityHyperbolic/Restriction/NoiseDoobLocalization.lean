module

public import ConditionedStochasticStabilityHyperbolic.Restriction.GeometricLifting
public import ConditionedStochasticStabilityHyperbolic.Restriction.DoobLocalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.Eigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure

/-!
# Product-measure localization for the actual noisy live kernel

Real bounded harmonic data construct the ENNReal Doob data. Robust geometric
certificates then localize the density product, both on the literal live
subtype and after pushing it into the ambient space. No independent Doob
data, invariant measure, or product-support hypothesis is supplied.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

section RealData

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- The real Bochner harmonic equation gives the exact nonnegative Doob
harmonic equation, including eigenfunctions with zeros. -/
def realEigenData (L : Kernel Y Y) [IsFiniteKernel L] (g : Y →ᵇ ℝ)
    (hg : ∀ y, 0 ≤ g y) (r : ℝ) (hr : 0 < r)
    (heigen : ∀ x, ∫ y, g y ∂L x = r * g x) :
    AbsorbingMarkovChains.DoobTransform.EigenData L where
  rate := ENNReal.ofReal r
  rate_ne_zero := ENNReal.ofReal_ne_zero_iff.mpr hr
  rate_ne_top := ENNReal.ofReal_ne_top
  weight := fun y => ENNReal.ofReal (g y)
  measurable_weight := g.continuous.measurable.ennreal_ofReal
  weight_ne_top := fun _ => ENNReal.ofReal_ne_top
  right_eigen := fun x => by
    rw [← ofReal_integral_eq_lintegral_ofReal (g.integrable (L x)) (ae_of_all _ hg),
      heigen x, ENNReal.ofReal_mul hr.le]

/-- Support and mass localization with a closed retained set, directly
from real harmonic data and the three actual kernel certificates. -/
theorem real_eigenvectorMeasure_localization
    (L : Kernel Y Y) [IsFiniteKernel L] (g : Y →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y)
    (r : ℝ) (hr : 0 < r) (heigen : ∀ x, ∫ y, g y ∂L x = r * g x)
    (μ : Measure Y) (hleft : L ∘ₘ μ = ENNReal.ofReal r • μ)
    (V : Set Y) (hV : IsClosed V) (hmV : MeasurableSet V) (B : Set Y)
    (hreturn : ∀ x ∈ V, ∀ᵐ y ∂L x, y ∉ V → y ∈ B)
    (hbad : ∀ x ∈ B, ∃ n : ℕ, (L ^ n) x univ = 0) (N : ℕ)
    (hcomp : ∀ x : ↥(Vᶜ), ((LeanShared.SubtypeKernel.restrict L Vᶜ hmV.compl) ^ N)
      x univ = 0) :
    LeanShared.eigenvectorMeasure μ g Vᶜ = 0 ∧
      (LeanShared.eigenvectorMeasure μ g).support ⊆ V := by
  let d := realEigenData L g hg r hr heigen
  have hz : LeanShared.eigenvectorMeasure μ g Vᶜ = 0 :=
    doob_weightedMeasure_complement_zero d μ hleft V hmV B hreturn hbad N hcomp
  exact ⟨hz, Measure.support_subset_of_isClosed hV hz⟩

end RealData

section MappedProduct

variable {X : Type*} [MeasurableSpace X]

/-- Pushing the literal-subtype density product into the ambient space is
the ambient density product for any measurable extension of the density. -/
theorem map_eigenvectorMeasure_of_extension (K : Set X) (μ : Measure K)
    (g : K → ℝ) (ga : X → ℝ) (hga : Measurable ga) (hmatch : ∀ x : K, ga x.val = g x) :
    (LeanShared.eigenvectorMeasure μ g).map Subtype.val =
      LeanShared.eigenvectorMeasure (μ.map Subtype.val) ga := by
  ext A hA
  rw [Measure.map_apply measurable_subtype_coe hA]
  unfold LeanShared.eigenvectorMeasure
  rw [withDensity_apply _ (hA.preimage measurable_subtype_coe), withDensity_apply _ hA,
    Measure.restrict_map measurable_subtype_coe hA,
    lintegral_map hga.ennreal_ofReal measurable_subtype_coe]
  apply lintegral_congr
  intro x
  rw [hmatch]

/-- The measurable ambient zero extension is valid for measures, without
claiming continuity across the boundary of the closed live set. -/
theorem map_eigenvectorMeasure_zeroExtend (K : Set X) (hK : MeasurableSet K)
    (μ : Measure K) (g : K → ℝ) (hg : Measurable g) :
    (LeanShared.eigenvectorMeasure μ g).map Subtype.val =
      LeanShared.eigenvectorMeasure (μ.map Subtype.val) (LeanShared.SubtypeKernel.zeroExtend K g) :=
  map_eigenvectorMeasure_of_extension K μ g _
    (LeanShared.SubtypeKernel.measurable_zeroExtend K hK g hg)
    (LeanShared.SubtypeKernel.zeroExtend_coe K g)

end MappedProduct

section GeometricNoise

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]

/-- Robust neighborhood geometry supplies every no-return and extinction
input for localization of the actual noisy product measure. The inclusion
into an ambient open set is retained explicitly for positivity consumers. -/
theorem exists_noise_eigenvectorMeasure_localization
    (T : X ≃ₜ X) (K U O : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ LeanShared.forwardTrapped T K ⊆ U)
    (hUO : closure U ⊆ O)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
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
  obtain ⟨N, _hN, δ, hδ, hcert⟩ := exists_geometric_lifting_certificates
    T K U S hK hU Metric.isOpen_thickening hcore (Metric.self_subset_thickening hr₀ _)
    ρ w hw W hW hwW
  refine ⟨min δ r₀, lt_min hδ hr₀, ?_⟩
  intro F hF hclose
  have hcloseδ : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ :=
    fun x hx ω => (hclose x hx ω).trans_le (min_le_left _ _)
  have hnoise : ∀ x ∈ K, x ∈ closure U → ∀ ω, F (x, ω) ∉ S \ U := by
    intro x _hx hxU ω
    exact hnonreturn (fun y => F (y, ω))
      (fun y hy => (hclose y (hUK hy) ω).trans_le (min_le_right _ _)) x hxU
  obtain ⟨hreturn, hbad, hcomp⟩ := hcert F hF hcloseδ hnoise
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

end GeometricNoise

section RankOneData

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (L : Kernel Y Y) [IsFiniteKernel L] (P : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
  (hP : ∀ (f : Y →ᵇ ℝ) (x : Y), P f x = ∫ y, f y ∂L x)

include hP in
omit [CompactSpace Y] [BorelSpace Y] [IsFiniteKernel L] in
/-- Positivity is a consequence of representing the actual positive kernel. -/
theorem representedTransfer_positive (f : Y →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : Y) :
    0 ≤ P f x := by
  rw [hP]
  exact integral_nonneg hf

/-- The leading measure is constructed by Riesz representation from the
positive rank-one functional. -/
def rankOneKernelMeasure (d : RankOneSpectralData P (1 : Y →ᵇ ℝ)) : Measure Y :=
  d.eigenmeasure (representedTransfer_positive L P hP)

instance rankOneKernelMeasure_finite (d : RankOneSpectralData P (1 : Y →ᵇ ℝ)) :
    IsFiniteMeasure (rankOneKernelMeasure L P hP d) := by
  unfold rankOneKernelMeasure
  infer_instance

include hP in
/-- Both genuine Doob eigenrelations and nonnegativity are derived from
rank-one data and the actual kernel representation. -/
theorem rankOneKernelMeasure_harmonic (d : RankOneSpectralData P (1 : Y →ᵇ ℝ)) :
    (∀ x, 0 ≤ d.eigenvector x) ∧
    (∀ x, ∫ y, d.eigenvector y ∂L x = d.rate * d.eigenvector x) ∧
    L ∘ₘ rankOneKernelMeasure L P hP d = ENNReal.ofReal d.rate • rankOneKernelMeasure L P hP d := by
  refine ⟨d.eigenvector_nonneg_of_positive (representedTransfer_positive L P hP), ?_, ?_⟩
  · intro x
    rw [← hP]
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul] using
      congrArg (fun f : Y →ᵇ ℝ => f x) d.right_eigenvector
  · exact rankOne_left_eigenmeasure d L hP (rankOneKernelMeasure L P hP d)
      (d.eigenmeasure_represents (representedTransfer_positive L P hP))

omit [IsFiniteKernel L] in
/-- The rank-one normalization makes the constructed density product a
probability measure; the leading measure itself need not have mass one. -/
theorem rankOneKernelMeasure_product_probability (d : RankOneSpectralData P (1 : Y →ᵇ ℝ)) :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure (rankOneKernelMeasure L P hP d)
      d.eigenvector) := by
  apply LeanShared.eigenvectorMeasure_isProbability _ _ (d.eigenvector.integrable _)
    (d.eigenvector_nonneg_of_positive (representedTransfer_positive L P hP))
  unfold rankOneKernelMeasure
  rw [← d.eigenmeasure_represents (representedTransfer_positive L P hP), d.mean_eigenvector]

end RankOneData

section RankOneGeometricNoise

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]

/-- For the actual full live kernel, rank-one spectral data alone construct
the product measure whose support is localized by the robust geometry.
`CompactSpace K` is the instance induced by the stated compactness of `K`. -/
theorem exists_noise_rankOne_product_localization
    (T : X ≃ₜ X) (K U O : Set X) [CompactSpace K] (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ LeanShared.forwardTrapped T K ⊆ U)
    (hUO : closure U ⊆ O)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
      ∀ (P : (K →ᵇ ℝ) →L[ℝ] (K →ᵇ ℝ)),
      (∀ (f : K →ᵇ ℝ) (x : K), P f x = ∫ y, f y ∂C.killedTransition x) →
      ∀ (d : RankOneSpectralData P (1 : K →ᵇ ℝ)),
      ∃ μ : Measure K, IsFiniteMeasure μ ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
        LeanShared.eigenvectorMeasure μ d.eigenvector (retainedRegion K U)ᶜ = 0 ∧
        (LeanShared.eigenvectorMeasure μ d.eigenvector).support ⊆ retainedRegion K U ∧
        ((LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val).support ⊆ closure U ∧
        ((LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val).support ⊆ O := by
  obtain ⟨δ, hδ, hloc⟩ := exists_noise_eigenvectorMeasure_localization
    T K U O hK hU hcore hUK hsep hUO ρ w hw W hW hwW
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose
  dsimp only
  intro P hP d
  let C := RestrictedNoise.chain ρ F hF K hK.isClosed.measurableSet w hw W hW hwW
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let μ := rankOneKernelMeasure C.killedTransition P hP d
  obtain ⟨hg, heigen, hleft⟩ := rankOneKernelMeasure_harmonic C.killedTransition P hP d
  refine ⟨μ, inferInstance, ?_, hloc F hF hclose d.eigenvector hg d.rate d.rate_pos heigen μ hleft⟩
  exact d.eigenmeasure_represents (representedTransfer_positive C.killedTransition P hP)

end RankOneGeometricNoise

end ConditionedStochasticStabilityHyperbolic.Restriction
