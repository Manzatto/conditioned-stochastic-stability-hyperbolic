module

public import LeanShared.Probability.KernelAdjointDensity
public import LeanShared.Probability.EigenvectorDensityPair
public import LeanShared.Dynamics.ReversibleTransitivity
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseWeightedPositivity
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveEigenfunction

/-!
# Positivity of the genuine inverse density

The original left density equation and actual forward/inverse kernel
duality derive the inverse right harmonic law. The original right law
derives the inverse left eigenmeasure. The forward normalized localized
product is the same measure after swapping the two densities. Thus the
weighted inverse noise positivity theorem requires no independent inverse
eigenrelations or inverse product-localization hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace ConditionedStochasticStabilityHyperbolic.InverseDensityPositivity

open LeanShared LeanShared.ControlledPlaqueClosure
open LocalPositiveEigenfunction

section Duality

variable {X : Type*} [MeasurableSpace X]

/-- The actual bilinear identity is symmetric after exchanging tests. -/
theorem isAdjoint_symm (J L : Kernel X X) (σ : Measure X)
    (hdual : KernelAdjointDensity.IsAdjoint J L σ) :
    KernelAdjointDensity.IsAdjoint L J σ :=
  fun f h hf hh => (hdual h f hh hf).symm

/-- The forward right law derives the inverse left eigenmeasure law. -/
theorem inverse_left_of_forward_right (J L : Kernel X X) (σ : Measure X)
    (hdual : KernelAdjointDensity.IsAdjoint J L σ) (g : X → ℝ≥0∞) (hg : Measurable g)
    (r : ℝ≥0∞) (hright : (fun x => ∫⁻ y, g y ∂J x) =ᵐ[σ] (fun x => r * g x)) :
    L ∘ₘ σ.withDensity g = r • σ.withDensity g := by
  rw [KernelAdjointDensity.comp_withDensity L J σ (isAdjoint_symm J L σ hdual) g hg,
    withDensity_congr_ae hright]
  change σ.withDensity (r • g) = _
  exact withDensity_smul r hg

/-- Only the actual forward Bochner law and integrability are needed to
produce its nonnegative harmonic law. -/
theorem lintegral_right_of_real_right (J : Kernel X X) (σ : Measure X)
    (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x) (r : ℝ) (hr : 0 ≤ r)
    (hint : ∀ᵐ x ∂σ, Integrable g (J x))
    (hright : (fun x => ∫ y, g y ∂J x) =ᵐ[σ] (fun x => r * g x)) :
    (fun x => ∫⁻ y, ENNReal.ofReal (g y) ∂J x) =ᵐ[σ]
      (fun x => ENNReal.ofReal r * ENNReal.ofReal (g x)) := by
  filter_upwards [hint, hright] with x hi hx
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hg0), hx,
    ENNReal.ofReal_mul hr]

end Duality

section Integrability

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω]

/-- Continuity on the compact live region and a bound at this departure
point give Bochner integrability for the actual noise-weighted kernel. -/
theorem integrable_weighted_killed (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (W : X × Ω → ℝ) (hW : Measurable W) (H : X × Ω → X) (hH : Measurable H)
    (K : Set X) (hK : IsCompact K) (m : X → ℝ) (hmc : ContinuousOn m K)
    (x : X) (B : ℝ) (hB : ∀ ω, W (x, ω) ≤ B) :
    Integrable m (WeightedRandomMapKernel.killed ρ W H K hK.measurableSet x) := by
  let : IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))) :=
    NoiseWeightedPositivity.weighted_law_isFinite ρ W hW x B hB
  let : IsFiniteMeasure (WeightedRandomMapKernel.transition ρ W H x) := by
    rw [WeightedRandomMapKernel.transition_apply ρ W hW H hH x]
    infer_instance
  exact hmc.integrableOn_compact hK

/-- A density continuous on the compact actual reference support produces
a finite density-weighted measure. Ambient continuity is unnecessary. -/
theorem finite_density_on_support (σ : Measure X) [IsFiniteMeasure σ] [σ.Regular]
    (K : Set X) (hK : IsCompact K) (hsupport : σ.support = K)
    (g : X → ℝ) (hgc : ContinuousOn g K) :
    IsFiniteMeasure (σ.withDensity (fun x => ENNReal.ofReal (g x))) := by
  have hσK : K ∈ ae σ := hsupport ▸ Measure.support_mem_ae_of_regular
  have hr : σ.restrict K = σ := Measure.restrict_eq_self_of_ae_mem hσK
  have hi : Integrable g (σ.restrict K) := hgc.integrableOn_compact hK
  rw [hr] at hi
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

end Integrability

section Assembly

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

/-- Step 4 for the actual inverse state-and-noise-weighted kernel. The
reference support is the compact live region. Original forward left/right
laws derive both inverse eigenrelations; the forward product supplies the
inverse normalization and localization by the checked density swap.

Compactness here is the paper's compact ambient manifold model. A separate
Euclidean change-of-variables chart bridge does not assert that a nonzero
Euclidean vector space is compact. -/
theorem exists_noise_tolerance_for_inverse_density_positivity
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      ForwardPlaqueInputs T.symm H V K G →
      ∀ (W : X × Ω → ℝ) (_hW : Measurable W) (B : ℝ),
      (∀ x ∈ K, ∀ ω, W (x, ω) ≤ B) → (∀ x ∈ K, ∀ ω, 0 < W (x, ω)) →
      let L := WeightedRandomMapKernel.killed ρ W H K hK.measurableSet
      ∀ (J : Kernel X X) [IsFiniteKernel J] (σ : Measure X) [IsFiniteMeasure σ],
      σ.support = K → (∀ x ∈ K, (J x).restrict K = J x) →
      KernelAdjointDensity.IsAdjoint J L σ →
      ∀ (g m : X → ℝ), Measurable g → Measurable m →
      (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ m x) → ContinuousOn g K → ContinuousOn m K →
      ContinuousOn (fun x => ∫ y, m y ∂L x) K →
      ∀ (r : ℝ), 0 < r →
      J ∘ₘ eigenvectorMeasure σ m = ENNReal.ofReal r • eigenvectorMeasure σ m →
      (∀ x ∈ K, ∫ y, g y ∂J x = r * g x) →
      (∫ x, g x ∂eigenvectorMeasure σ m) = 1 →
      (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V →
        IsFiniteMeasure (eigenvectorMeasure σ g) ∧ (eigenvectorMeasure σ g).Regular ∧
        L ∘ₘ eigenvectorMeasure σ g = ENNReal.ofReal r • eigenvectorMeasure σ g ∧
        (∀ x ∈ K, ∫ y, m y ∂L x = r * m x) ∧
        ∀ x ∈ isolatedCore T K, 0 < m x := by
  have hcore : isolatedCore T.symm K = isolatedCore T K := by
    simp only [isolatedCore, Homeomorph.symm_symm, inter_comm]
  obtain ⟨δ, hδ, hpos⟩ := NoiseWeightedPositivity.exists_pos_noise_tolerance_for_actual_core_positivity
    (Ω := Ω) T.symm V K G hV hVK hK hG (hcore ▸ hcoreV) (hcore ▸ hcoreG)
    (ReversibleTransitivity.isolatedCore_transitive_symm T K htrans)
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ H hH hclose hp W hW B hB hWpos
  dsimp only
  intro J _ σ _ hσsupport hJtarget hdual g m hg hm hg0 hm0 hgc hmc hLmc r hr hleft hright hnorm hlocal
  let L := WeightedRandomMapKernel.killed ρ W H K hK.measurableSet
  have hσK : K ∈ ae σ := hσsupport ▸ Measure.support_mem_ae_of_regular
  have hmInt : ∀ᵐ x ∂σ, Integrable m (L x) := by
    filter_upwards [hσK] with x hx
    exact integrable_weighted_killed ρ W hW H hH K hK m hmc x B (hB x hx)
  have hmharmonic : ∀ x ∈ K, ∫ y, m y ∂L x = r * m x :=
    KernelAdjointDensity.real_density_eigen_on_set J L σ hdual K hσsupport m hm hm0 r hr.le
      hleft hmInt hmc hLmc
  have hgInt : ∀ᵐ x ∂σ, Integrable g (J x) := by
    filter_upwards [hσK] with x hx
    have hi : Integrable g ((J x).restrict K) := hgc.integrableOn_compact hK
    rwa [hJtarget x hx] at hi
  have hgRight : (fun x => ∫ y, g y ∂J x) =ᵐ[σ] (fun x => r * g x) := by
    filter_upwards [hσK] with x hx
    exact hright x hx
  have hinverseleft : L ∘ₘ eigenvectorMeasure σ g = ENNReal.ofReal r • eigenvectorMeasure σ g :=
    inverse_left_of_forward_right J L σ hdual _ hg.ennreal_ofReal _
      (lintegral_right_of_real_right J σ g hg0 r hr.le hgInt hgRight)
  let : IsFiniteMeasure (eigenvectorMeasure σ g) :=
    finite_density_on_support σ K hK hσsupport g hgc
  have hregular : (eigenvectorMeasure σ g).Regular := inferInstance
  have hinversenorm : ∫ x, m x ∂eigenvectorMeasure σ g = 1 := by
    rw [← EigenvectorDensityPair.integral_comm σ g m hg hm hg0 hm0]
    exact hnorm
  have hinverselocal : (eigenvectorMeasure (eigenvectorMeasure σ g) m).support ⊆ V := by
    rw [← EigenvectorDensityPair.product_comm σ g m hg hm]
    exact hlocal
  refine ⟨inferInstance, hregular, hinverseleft, hmharmonic, ?_⟩
  have hpositive : ∀ x ∈ isolatedCore T.symm K, 0 < m x :=
    hpos ρ H hH hp.zero hp.continuous_noise hp.zero_noise (fun ω x hx => hclose x hx ω)
      hp.local_cover hp.plaque hp.lower_semicontinuous hp.backward_orbit hp.capture
      W hW B hB hWpos (eigenvectorMeasure σ g) hregular (ENNReal.ofReal r)
      (ENNReal.ofReal_ne_zero_iff.mpr hr) hinverseleft m hm hmc (fun x _ => hm0 x)
      r hmharmonic hinversenorm hinverselocal
  simpa only [hcore] using hpositive

/-- The inverse positivity just derived, together with the already proved
forward core positivity, places the whole isolated core in the genuine
normalized forward density-product support. -/
theorem exists_noise_tolerance_for_core_subset_product_support
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      ForwardPlaqueInputs T.symm H V K G →
      ∀ (W : X × Ω → ℝ) (_hW : Measurable W) (B : ℝ),
      (∀ x ∈ K, ∀ ω, W (x, ω) ≤ B) → (∀ x ∈ K, ∀ ω, 0 < W (x, ω)) →
      let L := WeightedRandomMapKernel.killed ρ W H K hK.measurableSet
      ∀ (J : Kernel X X) [IsFiniteKernel J] (σ : Measure X) [IsFiniteMeasure σ],
      σ.support = K → (∀ x ∈ K, (J x).restrict K = J x) →
      KernelAdjointDensity.IsAdjoint J L σ →
      ∀ (g m : X → ℝ), Measurable g → Measurable m →
      (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ m x) → ContinuousOn g K → ContinuousOn m K →
      ContinuousOn (fun x => ∫ y, m y ∂L x) K →
      ∀ (r : ℝ), 0 < r →
      J ∘ₘ eigenvectorMeasure σ m = ENNReal.ofReal r • eigenvectorMeasure σ m →
      (∀ x ∈ K, ∫ y, g y ∂J x = r * g x) →
      (∫ x, g x ∂eigenvectorMeasure σ m) = 1 →
      (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V →
      (∀ x ∈ isolatedCore T K, 0 < g x) →
        isolatedCore T K ⊆ (eigenvectorMeasure (eigenvectorMeasure σ m) g).support := by
  obtain ⟨δ, hδ, hcert⟩ := exists_noise_tolerance_for_inverse_density_positivity
    (Ω := Ω) T V K G hV hVK hK hG hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ H hH hclose hp W hW B hB hWpos
  dsimp only
  intro J _ σ _ hσsupport hJtarget hdual g m hg hm hg0 hm0 hgc hmc hLmc r hr
    hleft hright hnorm hlocal hgpos
  obtain ⟨_hfinite, _hregular, _hinverseleft, _hmharmonic, hmpos⟩ :=
    hcert ρ H hH hclose hp W hW B hB hWpos J σ hσsupport hJtarget hdual g m hg hm
      hg0 hm0 hgc hmc hLmc r hr hleft hright hnorm hlocal
  have hσK : K ∈ ae σ := hσsupport ▸ Measure.support_mem_ae_of_regular
  have hAK : isolatedCore T K ⊆ K := fun _ hx => forwardTrapped_subset T K hx.1
  have hAσ : isolatedCore T K ⊆ σ.support := by rwa [hσsupport]
  exact EigenvectorDensityPair.subset_support_product σ K (isolatedCore T K) hσK hAσ hAK
    g m hg hm hgc hmc hgpos hmpos

end Assembly

end ConditionedStochasticStabilityHyperbolic.InverseDensityPositivity
