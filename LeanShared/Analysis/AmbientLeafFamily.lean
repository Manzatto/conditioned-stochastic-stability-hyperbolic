module

public import LeanShared.Analysis.AmbientJetComponent

/-!
# Supremum norms over a specified family of genuine leaves

The paper takes its supremum over its own cone-compatible leaf family, not
over every bounded-density graph. A specified family defines its actual
complete ambient L¹ supremum target. Restriction from the proved
larger graph target is a contraction, so every constructed compact smoothing
operator remains compact on this exact family. No equivalence between the
larger family and the manuscript's cone family is asserted or assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BoundedContinuousFunction

namespace LeanShared.GraphLeafNorm

variable {A U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E] {J : ℝ}
  (μ : Measure U) (leaves : A → GraphLeaf U E J)

abbrev AmbientFamilySpace := lp (fun a : A => Lp ℂ 1 ((leaves a).measure μ)) ∞

def restrictFamilyLinearMap : AmbientLeafSpace (E := E) μ (J := J) →ₗ[ℂ]
    AmbientFamilySpace μ leaves where
  toFun z := ⟨fun a => z (leaves a), memℓp_infty ⟨‖z‖, by
    rintro _ ⟨a, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z (leaves a)⟩⟩
  map_add' x y := by
    apply lp.ext
    funext a
    rfl
  map_smul' c x := by
    apply lp.ext
    funext a
    rfl

def restrictFamily : AmbientLeafSpace (E := E) μ (J := J) →L[ℂ] AmbientFamilySpace μ leaves :=
  (restrictFamilyLinearMap μ leaves).mkContinuous 1 (fun z => by
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg z) fun a =>
      lp.norm_apply_le_norm ENNReal.top_ne_zero z (leaves a))

@[simp] theorem restrictFamily_apply (z : AmbientLeafSpace (E := E) μ (J := J)) (a : A) :
    restrictFamily μ leaves z a = z (leaves a) := rfl

theorem restrictFamily_norm_le : ‖restrictFamily μ leaves‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  exact lp.norm_le_of_forall_le (norm_nonneg z) fun a =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero z (leaves a)

end LeanShared.GraphLeafNorm

namespace LeanShared.SchwartzJetKernel

open SchwartzJetSpace

variable {E I U A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
  {K : Set E} (w : I → List E) (hK : IsCompact K) (χ ψ : 𝓢(E, ℂ))
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))
  (hχ : ∀ y ∉ K, χ y = 0) (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  (p : B →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (C : ℝ) (hC : 0 ≤ C)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖p b f‖ ≤ C * ‖b‖ * ‖jetMap K w f‖)

def familyDistributionOperator : B →L[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves :=
  (GraphLeafNorm.restrictFamily μ leaves).comp
    (ambientDistributionOperator w hK χ ψ μ hJ k hk hχ p C hC horder)

theorem familyDistributionOperator_isCompact :
    IsCompactOperator (familyDistributionOperator w hK χ ψ μ hJ k hk hχ leaves p C hC horder) :=
  (ambientDistributionOperator_isCompact w hK χ ψ μ hJ k hk hχ p C hC horder).clm_comp
    (GraphLeafNorm.restrictFamily μ leaves)

theorem familyDistributionOperator_ae (b : B) (a : A) :
    familyDistributionOperator w hK χ ψ μ hJ k hk hχ leaves p C hC horder b a
      =ᵐ[(leaves a).measure μ] fun x => p b (cutoffKernel χ ψ x) :=
  ambientDistributionOperator_ae w hK χ ψ μ hJ k hk hχ p C hC horder b (leaves a)

end LeanShared.SchwartzJetKernel
