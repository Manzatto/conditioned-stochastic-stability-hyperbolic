module

public import LeanShared.Analysis.AmbientSchwartzComponent
public import LeanShared.Analysis.SchwartzJetRepresentation

/-!
# Actual supported jet smoothing in ambient graph L¹

The finite Leibniz expansion and Hahn–Banach descent land in the actual
ambient pushforward measures. The constructed distribution representation
then gives a compact smoothing operator with exact original test pairings. Only a finite-order distribution bound is supplied, not a representation map,
an ambient norm comparison, or component compactness.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzJetKernel

open SchwartzJetSpace

variable {E I U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
  {K : Set E} (w : I → List E) (hK : IsCompact K) (χ ψ : 𝓢(E, ℂ))
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))

def ambientFullOperator : ((I → K →ᵇ ℂ) →L[ℂ] ℂ) →L[ℂ]
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) :=
  (SchwartzLeafComponent.ambientOperator hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk).comp (expandFunctional w)

theorem ambientFullOperator_isCompact :
    IsCompactOperator (ambientFullOperator w hK χ ψ μ hJ k hk) :=
  (SchwartzLeafComponent.ambientOperator_isCompact hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk).comp_clm (expandFunctional w)

theorem ambientFullOperator_ae (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ)
    (L : GraphLeafNorm.GraphLeaf U E J) :
    ambientFullOperator w hK χ ψ μ hJ k hk f L =ᵐ[L.measure μ]
      fun x => f (jetMap K w (cutoffKernel χ ψ x)) := by
  apply (SchwartzLeafComponent.ambientOperator_ae hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk (expandFunctional w f) L).trans
  exact ae_of_all _ fun x => congrArg f (sumMap_kernelSection w χ ψ x)

variable (hχ : ∀ y ∉ K, χ y = 0)

include hχ in
theorem ambientFullOperator_restriction_compatible (f g : (I → K →ᵇ ℂ) →L[ℂ] ℂ)
    (hfg : ∀ v : jetSpace K w, f v = g v) :
    ambientFullOperator w hK χ ψ μ hJ k hk f =
      ambientFullOperator w hK χ ψ μ hJ k hk g := by
  apply lp.ext
  funext L
  apply Lp.ext
  filter_upwards [ambientFullOperator_ae w hK χ ψ μ hJ k hk f L,
    ambientFullOperator_ae w hK χ ψ μ hJ k hk g L] with x hf hg
  rw [hf, hg]
  exact hfg ⟨_, cutoffKernel_jet_mem w χ ψ hχ x⟩

def ambientOperator : (jetSpace K w →L[ℂ] ℂ) →L[ℂ]
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) :=
  DualRestrictionCompactness.descend (jetSpace K w) (ambientFullOperator w hK χ ψ μ hJ k hk)
    (ambientFullOperator_restriction_compatible w hK χ ψ μ hJ k hk hχ)

theorem ambientOperator_isCompact :
    IsCompactOperator (ambientOperator w hK χ ψ μ hJ k hk hχ) :=
  DualRestrictionCompactness.descend_isCompact (jetSpace K w)
    (ambientFullOperator w hK χ ψ μ hJ k hk)
    (ambientFullOperator_restriction_compatible w hK χ ψ μ hJ k hk hχ)
    (ambientFullOperator_isCompact w hK χ ψ μ hJ k hk)

theorem ambientOperator_ae (f : jetSpace K w →L[ℂ] ℂ)
    (L : GraphLeafNorm.GraphLeaf U E J) :
    ambientOperator w hK χ ψ μ hJ k hk hχ f L =ᵐ[L.measure μ]
      fun x => f ⟨jetMap K w (cutoffKernel χ ψ x), cutoffKernel_jet_mem w χ ψ hχ x⟩ := by
  change ambientFullOperator w hK χ ψ μ hJ k hk
    (DualRestrictionCompactness.extension (jetSpace K w) f) L =ᵐ[_] _
  apply (ambientFullOperator_ae w hK χ ψ μ hJ k hk
    (DualRestrictionCompactness.extension (jetSpace K w) f) L).trans
  exact ae_of_all _ fun x => DualRestrictionCompactness.extension_apply (jetSpace K w) f
    ⟨_, cutoffKernel_jet_mem w χ ψ hχ x⟩

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  (p : B →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (C : ℝ) (hC : 0 ≤ C)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖p b f‖ ≤ C * ‖b‖ * ‖jetMap K w f‖)

def ambientDistributionOperator : B →L[ℂ]
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) :=
  (ambientOperator w hK χ ψ μ hJ k hk hχ).comp
    (SchwartzJetRepresentation.representation K w p C hC horder)

theorem ambientDistributionOperator_isCompact :
    IsCompactOperator (ambientDistributionOperator w hK χ ψ μ hJ k hk hχ p C hC horder) :=
  (ambientOperator_isCompact w hK χ ψ μ hJ k hk hχ).comp_clm
    (SchwartzJetRepresentation.representation K w p C hC horder)

theorem ambientDistributionOperator_ae (b : B) (L : GraphLeafNorm.GraphLeaf U E J) :
    ambientDistributionOperator w hK χ ψ μ hJ k hk hχ p C hC horder b L =ᵐ[L.measure μ]
      fun x => p b (cutoffKernel χ ψ x) := by
  apply (ambientOperator_ae w hK χ ψ μ hJ k hk hχ
    (SchwartzJetRepresentation.representation K w p C hC horder b) L).trans
  exact ae_of_all _ fun x =>
    SchwartzJetRepresentation.representation_cutoffKernel K w p C hC horder χ ψ hχ b x

end LeanShared.SchwartzJetKernel
