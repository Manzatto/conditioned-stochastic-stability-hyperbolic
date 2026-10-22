module

public import LeanShared.Analysis.AmbientLeafFamily
public import LeanShared.Analysis.DyadicCompletion

/-!
# Actual compact dyadic completions over a specified leaf family

The source is the closure of the explicit core block map in the supremum of
ambient graph-measure L¹ norms over precisely the supplied leaf family.
A supported distribution order bound constructs its jet-dual representation.
An almost-everywhere core convolution identity then identifies the constructed
compact normalized smoothing components with the actual coordinates by density.
The block bound one and geometric-tail compact weakening are conclusions.

The geometric/Fourier identification of the explicit core blocks and pairing
remains an input. No equivalence with a larger graph-leaf family is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.AmbientDyadicCompletion

variable {Core E I U S A : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype I]
  (w : I → List E) {K : Set E} (hK : IsCompact K)
  (χ : 𝓢(E, ℂ)) (hχ : ∀ y ∉ K, χ y = 0) (ψ : ℕ × S → 𝓢(E, ℂ))
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (q : Core →ₗ[ℂ] DyadicCompletion.BlockSpace
    (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := S))
  (p : DyadicCompletion.closedCore q →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ))
  (C : ℝ) (hC : 0 ≤ C)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖p b f‖ ≤ C * ‖b‖ * ‖SchwartzJetSpace.jetMap K w f‖)
  (t : S → ℝ)

/-- Actual smoothing on the distribution pairing, with representation
constructed from the order bound. -/
def component (j : ℕ × S) :
    DyadicCompletion.closedCore q →L[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves :=
  SchwartzJetKernel.familyDistributionOperator w hK χ (ψ j) μ hJ k hk hχ leaves p C hC horder

def normalizedComponent (j : ℕ × S) :
    DyadicCompletion.closedCore q →L[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves :=
  (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) • component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j

theorem normalizedComponent_ae (j : ℕ × S) (b : DyadicCompletion.closedCore q) (a : A) :
    normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j b a
      =ᵐ[(leaves a).measure μ] fun x =>
        (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) * p b (SchwartzJetKernel.cutoffKernel χ (ψ j) x) := by
  change (((((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) •
    component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j b) a) =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ)
    (component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j b a),
    SchwartzJetKernel.familyDistributionOperator_ae w hK χ (ψ j) μ hJ k hk hχ
      leaves p C hC horder b a] with x hs hp
  change (((((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) •
    component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j b a) :
      Lp ℂ 1 ((leaves a).measure μ)) x = _
  erw [hs]
  change (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) *
    (component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j b a) x = _
  exact congrArg (fun z : ℂ => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) * z) hp

theorem normalizedComponent_isCompact (j : ℕ × S) :
    IsCompactOperator (normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j) := by
  change IsCompactOperator (fun b => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) •
    component w hK χ hχ ψ μ hJ k hk leaves q p C hC horder j b)
  exact (SchwartzJetKernel.familyDistributionOperator_isCompact w hK χ (ψ j) μ hJ k hk hχ
    leaves p C hC horder).smul (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ)

variable (hcore : ∀ c : Core, ∀ j : ℕ × S, ∀ a : A,
  q c j a =ᵐ[(leaves a).measure μ] fun x =>
    (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) *
      p (DyadicCompletion.coreLift q c) (SchwartzJetKernel.cutoffKernel χ (ψ j) x))

include hcore hK hχ hJ hk hC horder in
/-- Actual AE convolution identification suffices for exact L¹/core equality. -/
theorem normalizedComponent_core (c : Core) (j : ℕ × S) :
    normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j
      (DyadicCompletion.coreLift q c) = q c j := by
  apply lp.ext
  funext a
  apply Lp.ext
  exact (normalizedComponent_ae w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t
    j (DyadicCompletion.coreLift q c) a).trans (hcore c j a).symm

include hcore hK hχ hJ hk hC horder in
/-- Density identifies every constructed normalized component with the
coordinate on the actual completed strong norm. -/
theorem normalizedComponent_eq_coordinate (b : DyadicCompletion.closedCore q) (j : ℕ × S) :
    normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j b =
      (b : DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := S)) j := by
  refine (DyadicCompletion.coreLift_dense q).induction_on
    (p := fun z => normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j z =
      (z : DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := S)) j)
    b ?_ (fun c => normalizedComponent_core w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore c j)
  exact isClosed_eq
    (normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j).continuous
    ((DyadicCompletion.coordinate j).comp (DyadicCompletion.closedCore q).subtypeL).continuous

include hcore hK hχ hJ hk hC horder in
theorem normalizedComponent_norm_le (j : ℕ × S) :
    ‖normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  rw [normalizedComponent_eq_coordinate w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore]
  rw [one_mul]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero b.val j

variable {η : ℝ} (hη : 0 < η)

/-- Actual dyadic smoothing with a strict exponent loss. -/
def operator : DyadicCompletion.closedCore q →L[ℂ]
    DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := S) :=
  DyadicCompactness.operator
    (normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t)
    zero_le_one (normalizedComponent_norm_le w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore)
    (DyadicCompactness.dyadicFactor_pos η).le (DyadicCompactness.dyadicFactor_lt_one hη).le

include hcore hK hχ hJ hk hC horder in
theorem operator_eq_reweight (b : DyadicCompletion.closedCore q) :
    operator w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore hη b =
      DyadicCompletion.reweight η hη b.val := by
  apply lp.ext
  funext j
  change ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) •
    normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t j b =
      ((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) • b.val j
  rw [normalizedComponent_eq_coordinate w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore]

include hcore hK hχ hJ hk hC horder in
theorem inclusion_isCompact [Fintype S] :
    IsCompactOperator (DyadicCompletion.inclusion q η hη) := by
  have heq : (DyadicCompletion.reweight η hη).comp (DyadicCompletion.closedCore q).subtypeL =
      operator w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore hη := by
    apply ContinuousLinearMap.ext
    intro b
    exact (operator_eq_reweight w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore hη b).symm
  apply DyadicCompletion.lift_isCompact
  rw [heq]
  exact DyadicCompactness.dyadic_operator_isCompact
    (normalizedComponent w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t)
    zero_le_one (normalizedComponent_norm_le w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore)
    hη (normalizedComponent_isCompact w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t)

include hcore hK hχ hJ hk hC horder in
theorem compact_injective_inclusion [Fintype S] :
    IsCompactOperator (DyadicCompletion.inclusion q η hη) ∧
      Function.Injective (DyadicCompletion.inclusion q η hη) :=
  ⟨inclusion_isCompact w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore hη,
    DyadicCompletion.inclusion_injective q η hη⟩

include hcore hK hχ hJ hk hC horder in
/-- Unequal branch losses are a common strict loss followed by the actual
nonnegative branch multipliers, between closures of their actual core ranges. -/
theorem compact_injective_exactInclusion [Fintype S] (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) :
    IsCompactOperator (DyadicCompletion.exactInclusion q η hη δ hδ) ∧
      Function.Injective (DyadicCompletion.exactInclusion q η hη δ hδ) :=
  ⟨DyadicCompletion.exactInclusion_isCompact q η hη δ hδ
      (inclusion_isCompact w hK χ hχ ψ μ hJ k hk leaves q p C hC horder t hcore hη),
    DyadicCompletion.exactInclusion_injective q η hη δ hδ⟩

end LeanShared.AmbientDyadicCompletion
