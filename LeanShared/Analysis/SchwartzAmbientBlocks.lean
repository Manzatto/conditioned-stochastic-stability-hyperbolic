module

public import LeanShared.Analysis.SchwartzAmbientRealization
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.DyadicCompletion

/-!
# Actual supported Schwartz core blocks in the specified ambient leaf norm

Physical Schwartz convolution blocks are realized in the ambient graph L¹
spaces of the supplied leaf family. The cited smooth-core boundedness estimate
is precisely finiteness of their weighted block supremum for each supported
test. It constructs the block core map into `lp∞`; the supremum norm and AE
physical convolution/cutoff pairing identities are then derived.

No distribution order bound, core injectivity, or compactness is assumed or
asserted here. A supplied leaf family need not separate smooth functions.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzAmbientBlocks

open SchwartzJetSpace

variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)

/-- An actual physical block, on the literal supported smooth core. -/
def block (j : ℕ × S) : supportedCore D →ₗ[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves :=
  (SchwartzAmbientRealization.linearMap μ hJ leaves).comp
    ((ConeFourierBlocks.block (σ j)).toLinearMap.comp (supportedCore D).subtype)

def weight (j : ℕ × S) : ℂ := (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ)

/-- The normalized physical block defining the strong core norm. -/
def weightedBlock (j : ℕ × S) :
    supportedCore D →ₗ[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves :=
  weight t j • block μ hJ leaves D σ j

/-- The precise cited smooth-core boundedness input. It supplies no global
operator, representation map, compactness, or distribution order estimate. -/
def SmoothCoreBounded : Prop :=
  ∀ f : supportedCore D, ∃ M : ℝ, ∀ j, ‖weightedBlock μ hJ leaves D σ t j f‖ ≤ M

variable (hbounded : SmoothCoreBounded μ hJ leaves D σ t)

/-- The actual core map into the ambient block supremum space. -/
def coreMap : supportedCore D →ₗ[ℂ]
    DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := S) where
  toFun f := ⟨fun j => weightedBlock μ hJ leaves D σ t j f, memℓp_infty (by
    obtain ⟨M, hM⟩ := hbounded f
    exact ⟨M, by rintro _ ⟨j, rfl⟩; exact hM j⟩)⟩
  map_add' f g := by
    apply lp.ext
    funext j
    exact (weightedBlock μ hJ leaves D σ t j).map_add f g
  map_smul' c f := by
    apply lp.ext
    funext j
    exact (weightedBlock μ hJ leaves D σ t j).map_smul c f

@[simp]
theorem coreMap_apply (f : supportedCore D) (j : ℕ × S) :
    coreMap μ hJ leaves D σ t hbounded f j = weightedBlock μ hJ leaves D σ t j f := rfl

/-- The constructed norm is exactly the weighted supremum over blocks,
where each block already takes the specified ambient leaf-family supremum. -/
theorem coreMap_norm (f : supportedCore D) :
    ‖coreMap μ hJ leaves D σ t hbounded f‖ =
      ⨆ j, ‖weightedBlock μ hJ leaves D σ t j f‖ := rfl

theorem coreMap_ae (f : supportedCore D) (j : ℕ × S) (a : A) :
    coreMap μ hJ leaves D σ t hbounded f j a =ᵐ[(leaves a).measure μ]
      fun x => weight t j * ConeFourierBlocks.block (σ j) f.val x := by
  change (weight t j • (SchwartzAmbientRealization.linearMap μ hJ leaves
    (ConeFourierBlocks.block (σ j) f.val) a)) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (weight t j) (SchwartzAmbientRealization.linearMap μ hJ leaves
    (ConeFourierBlocks.block (σ j) f.val) a),
    SchwartzAmbientRealization.linearMap_ae μ hJ leaves (ConeFourierBlocks.block (σ j) f.val) a]
    with x hs hf
  erw [hs]
  change weight t j * (SchwartzAmbientRealization.linearMap μ hJ leaves
    (ConeFourierBlocks.block (σ j) f.val) a) x = _
  exact congrArg (fun z : ℂ => weight t j * z) hf

/-- The original smooth-function distribution pairing, restricted to the
literal support core; no independent distribution realization is supplied. -/
def pairing : supportedCore D →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ) :=
  ConeFourierBlocks.integralPairing.comp (supportedCore D).subtype

theorem coreMap_cutoffPairing_ae (χ : 𝓢(E, ℂ)) (hχ : ∀ y ∈ D, χ y = 1)
    (f : supportedCore D) (j : ℕ × S) (a : A) :
    coreMap μ hJ leaves D σ t hbounded f j a =ᵐ[(leaves a).measure μ]
      fun x => weight t j * pairing D f
        (SchwartzJetKernel.cutoffKernel χ (FourierSchwartzKernel.kernel (σ j)) x) := by
  apply (coreMap_ae μ hJ leaves D σ t hbounded f j a).trans
  exact ae_of_all _ fun x => congrArg (fun z : ℂ => weight t j * z)
    (ConeFourierBlocks.integralPairing_cutoffKernel (σ j) f.val χ f.property hχ x).symm

end LeanShared.SchwartzAmbientBlocks
