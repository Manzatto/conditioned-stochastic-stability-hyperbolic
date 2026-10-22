module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseDensityPositivity
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseWeightedCollarPositivity

/-! The inverse support argument for weights that may vanish away from a
fixed two-sided positive collar. Original adjointness and real eigenlaws
construct the inverse pair; actual stationary product parents replace
positivity on the entire closed survival set. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ConditionedStochasticStabilityHyperbolic.InverseCollarDensityPositivity

open LeanShared LocalPositiveEigenfunction Restriction InverseDensityPositivity
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

theorem exists_noise_tolerance_for_inverse_collar_density_positivity
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm H V K G →
      ∀ (W : X × Ω → ℝ) (_hW : Measurable W) (B : ℝ),
      (∀ x ∈ K, ∀ ω, W (x, ω) ≤ B) → (∀ x ∈ K, x ∈ G → ∀ ω, 0 < W (x, ω)) →
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
      (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V ∩ G →
        IsFiniteMeasure (eigenvectorMeasure σ g) ∧ (eigenvectorMeasure σ g).Regular ∧
        L ∘ₘ eigenvectorMeasure σ g = ENNReal.ofReal r • eigenvectorMeasure σ g ∧
        (∀ x ∈ K, ∫ y, m y ∂L x = r * m x) ∧
        ∀ x ∈ isolatedCore T K, 0 < m x := by
  have hcore : isolatedCore T.symm K = isolatedCore T K := by
    simp only [isolatedCore, Homeomorph.symm_symm, inter_comm]
  refine ⟨1, zero_lt_one, ?_⟩
  intro ρ _ _ H hH _hclose hp W hW B hB hWpos
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
  have hinverselocal : (eigenvectorMeasure (eigenvectorMeasure σ g) m).support ⊆ V ∩ G := by
    rw [← EigenvectorDensityPair.product_comm σ g m hg hm]
    exact hlocal
  refine ⟨inferInstance, hregular, hinverseleft, hmharmonic, ?_⟩
  have hpositive : ∀ x ∈ isolatedCore T.symm K, 0 < m x :=
    NoiseWeightedCollarPositivity.core_positive_of_actual_weighted_collar
      T.symm V K G hV hVK hK (hcore ▸ hcoreV) (hcore ▸ hcoreG)
      (ReversibleTransitivity.isolatedCore_transitive_symm T K htrans)
      ρ H hH hp W hW B hB hWpos (eigenvectorMeasure σ g) r hr hinverseleft
      m hm hmc hm0 hmharmonic hinversenorm hinverselocal
  simpa only [hcore] using hpositive

theorem exists_noise_tolerance_for_collar_core_subset_product_support
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm H V K G →
      ∀ (W : X × Ω → ℝ) (_hW : Measurable W) (B : ℝ),
      (∀ x ∈ K, ∀ ω, W (x, ω) ≤ B) → (∀ x ∈ K, x ∈ G → ∀ ω, 0 < W (x, ω)) →
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
      (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V ∩ G →
      (∀ x ∈ isolatedCore T K, 0 < g x) →
        isolatedCore T K ⊆ (eigenvectorMeasure (eigenvectorMeasure σ m) g).support := by
  obtain ⟨δ, hδ, hcert⟩ := exists_noise_tolerance_for_inverse_collar_density_positivity
    (Ω := Ω) T V K G hV hVK hK hcoreV hcoreG htrans
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

end ConditionedStochasticStabilityHyperbolic.InverseCollarDensityPositivity
