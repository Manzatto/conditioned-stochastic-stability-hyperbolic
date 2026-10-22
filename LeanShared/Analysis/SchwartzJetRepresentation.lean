module

public import LeanShared.Analysis.DistributionJetRepresentation
public import LeanShared.Analysis.SchwartzJetKernel

/-!
# Constructed finite-order Schwartz jet representations

A literal pairing with Schwartz tests and a distribution order bound on
supported tests construct the representation in the actual supported jet
dual. Composing with the constructed compact cutoff smoothing operator gives
a compact operator whose almost-everywhere values are the original test
pairing. No representation CLM or smoothing certificate is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzJetRepresentation

open SchwartzJetSpace

variable {B E I : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
  (K : Set E) (w : I → List E)
  (p : B →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ))
  (C : ℝ) (hC : 0 ≤ C)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖p b f‖ ≤ C * ‖b‖ * ‖jetMap K w f‖)

local instance jetNormedSpace : NormedSpace ℂ (jetSpace K w) := inferInstance
local instance jetDualNormedAddCommGroup : NormedAddCommGroup (jetSpace K w →L[ℂ] ℂ) :=
  inferInstance
local instance jetDualNormedSpace : NormedSpace ℂ (jetSpace K w →L[ℂ] ℂ) := inferInstance

/-- Restrict the literal distribution pairing to the supported test core. -/
def supportedPairing : B →ₗ[ℂ] (supportedCore K →ₗ[ℂ] ℂ) where
  toFun b := (p b).comp (supportedCore K).subtype
  map_add' b d := by
    ext f
    change p (b + d) f.val = p b f.val + p d f.val
    rw [map_add]
    rfl
  map_smul' c b := by
    ext f
    change p (c • b) f.val = c • p b f.val
    rw [map_smul]
    rfl

/-- The representation map is produced from the cited order estimate. -/
def representation : B →L[ℂ] (jetSpace K w →L[ℂ] ℂ) :=
  DistributionJetRepresentation.representation
    ((jetMap K w).comp (supportedCore K).subtype) (supportedPairing K p) C hC
    (fun b f => horder b f.val f.property)

@[simp]
theorem representation_test (b : B) (f : 𝓢(E, ℂ)) (hf : ∀ x ∉ K, f x = 0) :
    representation K w p C hC horder b ⟨jetMap K w f, jet_mem K w f hf⟩ = p b f := by
  exact DistributionJetRepresentation.representation_core
    ((jetMap K w).comp (supportedCore K).subtype) (supportedPairing K p) C hC
    (fun b f => horder b f.val f.property) b ⟨f, hf⟩

theorem representation_norm_le : ‖representation K w p C hC horder‖ ≤ C :=
  DistributionJetRepresentation.representation_norm_le _ _ C hC _

theorem representation_cutoffKernel (χ ψ : 𝓢(E, ℂ)) (hχ : ∀ y ∉ K, χ y = 0)
    (b : B) (x : E) :
    representation K w p C hC horder b
      ⟨jetMap K w (SchwartzJetKernel.cutoffKernel χ ψ x),
        SchwartzJetKernel.cutoffKernel_jet_mem w χ ψ hχ x⟩ =
      p b (SchwartzJetKernel.cutoffKernel χ ψ x) :=
  representation_test K w p C hC horder b _ (SchwartzJetKernel.cutoffKernel_supported χ ψ hχ x)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (hK : IsCompact K) (χ ψ : 𝓢(E, ℂ)) (hχ : ∀ y ∉ K, χ y = 0)
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))

/-- Actual compact smoothing of distributions from their order bound. -/
def operator : B →L[ℂ] GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  (SchwartzJetKernel.operator w hK χ ψ μ hJ k hk hχ).comp
    (representation K w p C hC horder)

theorem operator_isCompact :
    IsCompactOperator (operator K w p C hC horder hK χ ψ hχ μ hJ k hk) :=
  (SchwartzJetKernel.operator_isCompact w hK χ ψ μ hJ k hk hχ).comp_clm
    (representation K w p C hC horder)

/-- The constructed L¹ graph-leaf values are exactly the original
distribution paired with the translated cutoff kernel. -/
theorem operator_ae (b : B) (L : GraphLeafNorm.GraphLeaf U E J) :
    operator K w p C hC horder hK χ ψ hχ μ hJ k hk b L =ᵐ[L.sourceMeasure μ]
      fun y => p b (SchwartzJetKernel.cutoffKernel χ ψ (L.graph y)) := by
  apply (SchwartzJetKernel.operator_ae w hK χ ψ μ hJ k hk hχ
    (representation K w p C hC horder b) L).trans
  exact ae_of_all _ fun y => representation_cutoffKernel K w p C hC horder χ ψ hχ b (L.graph y)

end LeanShared.SchwartzJetRepresentation
