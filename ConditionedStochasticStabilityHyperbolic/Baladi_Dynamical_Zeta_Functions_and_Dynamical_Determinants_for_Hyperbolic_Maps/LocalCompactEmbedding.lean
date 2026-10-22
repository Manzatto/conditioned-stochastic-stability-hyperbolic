module

public import LeanShared.Analysis.AmbientDyadicCompletion
public import LeanShared.Analysis.LeafFamilySeparation

/-!
# Actual local compact embedding for a fixed cone and specified leaf family

The smooth core consists of supported Schwartz functions. Its blocks are the
actual physical convolutions of the genuine cone partition, realized in the
ambient L¹ supremum over the supplied family of cone-compatible leaves. The cited smooth-core boundedness and completed distribution order estimate
are explicit inputs, together with agreement of that distribution pairing
on the smooth core. The required smoothing/core identity is derived from
physical convolution and a cutoff equal to one on the core support.

Compactness and injection of strict same-cone weakening are conclusions. Leaf-support coverage also derives injectivity of the actual smooth core map. No global compactness or core smoothing identity is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.LocalCompactEmbedding

open LeanShared

variable {E U A I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) {Cplus Cminus : Set E} (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff Cplus Cminus) (t : Bool → ℝ)
  (hbounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D
    (ConeDyadicSymbols.symbols radial angle) t)

/-- The genuine strong smooth core, with its actual weighted ambient blocks. -/
abbrev coreMap := SchwartzAmbientBlocks.coreMap μ hJ leaves D
  (ConeDyadicSymbols.symbols radial angle) t hbounded

/-- Its actual complete strong space is the closure of that concrete range. -/
abbrev StrongSpace := DyadicCompletion.closedCore (coreMap μ hJ leaves D radial angle t hbounded)

theorem core_norm (f : SchwartzJetSpace.supportedCore D) :
    ‖coreMap μ hJ leaves D radial angle t hbounded f‖ =
      ⨆ j, ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D
        (ConeDyadicSymbols.symbols radial angle) t j f‖ := rfl

/-- Support coverage makes the actual strong core realization injective. -/
theorem core_injective (hcover : ∀ x : E, ∃ a, x ∈ ((leaves a).measure μ).support) :
    Function.Injective (coreMap μ hJ leaves D radial angle t hbounded) :=
  LeafFamilySeparation.coreMap_injective μ hJ leaves hcover D radial angle t hbounded

variable [Fintype I] (w : I → List E)
  {K : Set E} (hK : IsCompact K) (cutoff : 𝓢(E, ℂ))
  (hcutoff : ∀ y ∉ K, cutoff y = 0) (hone : ∀ y ∈ D, cutoff y = 1)
  (p : StrongSpace μ hJ leaves D radial angle t hbounded →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ))
  (C : ℝ) (hC : 0 ≤ C)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖p b f‖ ≤ C * ‖b‖ * ‖SchwartzJetSpace.jetMap K w f‖)
  (hpairing : ∀ (f : SchwartzJetSpace.supportedCore D) (test : 𝓢(E, ℂ)),
    p (DyadicCompletion.coreLift (coreMap μ hJ leaves D radial angle t hbounded) f) test =
      ConeFourierBlocks.integralPairing f.val test)

include hone hpairing in
/-- The physical block pairing theorem discharges the smoothing identity
needed by the generic compactness producer, as an equality of actual AE values. -/
theorem core_convolution_identity (f : SchwartzJetSpace.supportedCore D) (j : ℕ × Bool) (a : A) :
    coreMap μ hJ leaves D radial angle t hbounded f j a =ᵐ[(leaves a).measure μ]
      fun x => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) *
        p (DyadicCompletion.coreLift (coreMap μ hJ leaves D radial angle t hbounded) f)
          (SchwartzJetKernel.cutoffKernel cutoff
            (FourierSchwartzKernel.kernel (ConeDyadicSymbols.symbols radial angle j)) x) := by
  apply (SchwartzAmbientBlocks.coreMap_cutoffPairing_ae μ hJ leaves D
    (ConeDyadicSymbols.symbols radial angle) t hbounded cutoff hone f j a).trans
  exact ae_of_all _ fun x => congrArg
    (fun z : ℂ => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) * z) (hpairing f _).symm

variable {η : ℝ} (hη : 0 < η)

include hK hcutoff hone hC horder hpairing in
/-- The actual local compact, injective same-cone embedding. The right
space is the closure of the same physical blocks with a common strict loss. -/
theorem compact_injective_inclusion :
    IsCompactOperator (DyadicCompletion.inclusion (coreMap μ hJ leaves D radial angle t hbounded) η hη) ∧
      Function.Injective (DyadicCompletion.inclusion (coreMap μ hJ leaves D radial angle t hbounded) η hη) :=
  AmbientDyadicCompletion.compact_injective_inclusion w hK cutoff hcutoff
    (fun j => FourierSchwartzKernel.kernel (ConeDyadicSymbols.symbols radial angle j))
    μ hJ (SchwartzAmbientRealization.decayOrder (U := U)) (SchwartzAmbientRealization.decayOrder_gt (U := U))
    leaves (coreMap μ hJ leaves D radial angle t hbounded) p C hC horder t
    (core_convolution_identity μ hJ leaves D radial angle t hbounded cutoff hone p hpairing) hη

include hK hcutoff hone hC horder hpairing in
/-- The manuscript's two branches may lose different positive exponents:
one common strict loss and explicit nonnegative additional losses suffice. -/
theorem compact_injective_exactInclusion (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    IsCompactOperator (DyadicCompletion.exactInclusion
      (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ) ∧
      Function.Injective (DyadicCompletion.exactInclusion
        (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ) :=
  AmbientDyadicCompletion.compact_injective_exactInclusion w hK cutoff hcutoff
    (fun j => FourierSchwartzKernel.kernel (ConeDyadicSymbols.symbols radial angle j))
    μ hJ (SchwartzAmbientRealization.decayOrder (U := U)) (SchwartzAmbientRealization.decayOrder_gt (U := U))
    leaves (coreMap μ hJ leaves D radial angle t hbounded) p C hC horder t
    (core_convolution_identity μ hJ leaves D radial angle t hbounded cutoff hone p hpairing) hη δ hδ

/-- Canonical additional weakening of the actual smooth core. -/
def canonicalWeakCore (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :=
  DyadicCompletion.finalCore (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ

/-- Canonical scalar weakening is exactly the same physical block family
with the literal exponents `t(s) - η - δ(s)`. -/
theorem canonicalWeakCore_apply (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s)
    (f : SchwartzJetSpace.supportedCore D) (j : ℕ × Bool) :
    canonicalWeakCore μ hJ leaves D radial angle t hbounded hη δ hδ f j =
      SchwartzAmbientBlocks.weightedBlock μ hJ leaves D
        (ConeDyadicSymbols.symbols radial angle) (fun s => t s - η - δ s) j f := by
  have he := DyadicCompletion.exactInclusion_apply
    (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ
    (DyadicCompletion.coreLift (coreMap μ hJ leaves D radial angle t hbounded) f) j
  change canonicalWeakCore μ hJ leaves D radial angle t hbounded hη δ hδ f j = _ at he
  rw [he]
  change (((2 : ℝ) ^ (-(η + δ j.2) * j.1) : ℝ) : ℂ) •
      (SchwartzAmbientBlocks.weight t j • SchwartzAmbientBlocks.block μ hJ leaves D
        (ConeDyadicSymbols.symbols radial angle) j f) =
    SchwartzAmbientBlocks.weight (fun s => t s - η - δ s) j •
      SchwartzAmbientBlocks.block μ hJ leaves D (ConeDyadicSymbols.symbols radial angle) j f
  rw [smul_smul]
  congr 1
  unfold SchwartzAmbientBlocks.weight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by norm_num)]
  congr 2
  ring

include hbounded hη in
/-- The weak physical smooth-core bound is derived from the canonical
weakened block norm, rather than supplied as another cited estimate. -/
theorem weak_smoothCoreBounded (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D
      (ConeDyadicSymbols.symbols radial angle) (fun s => t s - η - δ s) := by
  intro f
  refine ⟨‖canonicalWeakCore μ hJ leaves D radial angle t hbounded hη δ hδ f‖, ?_⟩
  intro j
  rw [← canonicalWeakCore_apply μ hJ leaves D radial angle t hbounded hη δ hδ f j]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ j

/-- The literal physical weak core, constructed with its derived bound. -/
def weakCoreMap (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :=
  SchwartzAmbientBlocks.coreMap μ hJ leaves D (ConeDyadicSymbols.symbols radial angle)
    (fun s => t s - η - δ s)
    (weak_smoothCoreBounded μ hJ leaves D radial angle t hbounded hη δ hδ)

/-- The target core of the proved compact embedding is exactly the literal
physical weak-exponent core, so their actual completed ranges agree. -/
theorem weakCoreMap_eq_finalCore (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    weakCoreMap μ hJ leaves D radial angle t hbounded hη δ hδ =
      DyadicCompletion.finalCore (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ := by
  apply LinearMap.ext
  intro f
  apply lp.ext
  funext j
  exact (canonicalWeakCore_apply μ hJ leaves D radial angle t hbounded hη δ hδ f j).symm

theorem weak_completion_eq (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    DyadicCompletion.closedCore (weakCoreMap μ hJ leaves D radial angle t hbounded hη δ hδ) =
      DyadicCompletion.closedCore
        (DyadicCompletion.finalCore (coreMap μ hJ leaves D radial angle t hbounded) η hη δ hδ) :=
  congrArg DyadicCompletion.closedCore
    (weakCoreMap_eq_finalCore μ hJ leaves D radial angle t hbounded hη δ hδ)

end ConditionedStochasticStabilityHyperbolic.LocalCompactEmbedding
