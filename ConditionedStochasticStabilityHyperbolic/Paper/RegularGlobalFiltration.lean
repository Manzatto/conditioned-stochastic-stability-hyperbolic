module

public import ConditionedStochasticStabilityHyperbolic.Paper.NoiseSmallness
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationKernel
public import ConditionedStochasticStabilityHyperbolic.Global.ActualAbsorbingKernelSupport

/-! The literal represented perturbations supply the global filtration support
conditions before the driving law is chosen. Positive levels use adapted
compactness. The zero level uses the separately stated strict trapping gate.
No stochastic support or noisy invariance condition is a source assumption. -/

public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared Global
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem Representation.eventually_preserves_shifted_levels
    (p : Representation F Parameters evaluate) (N : ℕ) (A : Set M)
    (levels : ℕ → Set M) (ℓ : ℕ)
    (compact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i))
    (adapted : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i))) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ z : FixedControl (ι := ι),
      ∀ i, 0 < i → i ≤ ℓ → MapsTo (evaluate (p.fixedParameters ε z))
        (shiftedFiltration T N A levels i) (shiftedFiltration T N A levels i) := by
  obtain ⟨δ, hδ, preserve⟩ := exists_pos_finite_adapted_margin T T.continuous
    (fun j : Fin ℓ => shiftedFiltration T N A levels (j.val + 1))
    (fun j => by
      rw [shiftedFiltration_pos T N A levels (by omega : 0 < j.val + 1)]
      exact isCompact_preimage_iterate T (compact _ (by omega) (by omega)) N)
    (fun j => by
      rw [shiftedFiltration_pos T N A levels (by omega : 0 < j.val + 1)]
      intro x hx
      apply preimage_interior_subset_interior_preimage (T.continuous.iterate N)
      change (T : M → M)^[N] (T x) ∈ interior (levels (j.val + 1))
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact adapted _ (by omega) (by omega) hx)
  filter_upwards [F.eventually_uniform_close δ hδ,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε close window
  intro z i hi hiℓ x hx
  let j : Fin ℓ := ⟨i - 1, by omega⟩
  have heq : j.val + 1 = i := by dsimp [j]; omega
  have hp := preserve (evaluate (p.fixedParameters ε z))
    (fun _j y _hy => by rw [p.actual_fixedMap ε close.1 window.le]; exact close.2.2 y z) j
  rw [heq] at hp
  exact interior_subset (hp hx)

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_shifted_kernel_support
    (p : Representation F Parameters evaluate) (N : ℕ) (A : Set M)
    (hA : MeasurableSet A) (levels : ℕ → Set M) (ℓ : ℕ)
    (compact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i))
    (adapted : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i)))
    (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ L : Laws (ι := ι),
      ∀ i, 0 < i → i ≤ ℓ → ∀ x ∈ shiftedFiltration T N A levels i,
        (NoiseKernel.chain (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
          (p.allScale_measurable ε) Aᶜ hA.compl w hw R hR hwR).killedTransition x
          (shiftedFiltration T N A levels i)ᶜ = 0 := by
  filter_upwards [p.eventually_preserves_shifted_levels N A levels ℓ compact adapted] with ε preserve
  intro L i hi hiℓ
  have hc : IsCompact (shiftedFiltration T N A levels i) := by
    rw [shiftedFiltration_pos T N A levels hi]
    exact isCompact_preimage_iterate T (compact i hi hiℓ) N
  exact noise_chain_no_upward_transition (L.fixedLaw ε) _ (p.allScale_measurable ε)
    A hA w hw R hR hwR _ hc.isClosed.measurableSet (fun z => preserve z i hi hiℓ)

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_strict_absorbing_support [CompactSpace M]
    (p : Representation F Parameters evaluate) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A)
    (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ L : Laws (ι := ι),
      ∀ x ∈ A, (NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Aᶜ hA.measurableSet.compl w hw R hR hwR).killedTransition x Aᶜ = 0 := by
  obtain ⟨δ, hδ, preserve⟩ := ActualAbsorbingKernelSupport.exists_pos_uniform_absorbing_map_tolerance
    T T.continuous A hA strict
  filter_upwards [F.eventually_uniform_close δ hδ,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε close window
  intro L x hx
  apply ActualAbsorbingKernelSupport.no_surviving_departure_of_absorbing_invariant
    (L.fixedLaw ε) _ (p.allScale_measurable ε) A hA.measurableSet w hw R hR hwR
    (fun y hy z => ?_) x hx
  exact preserve (evaluate (p.fixedParameters ε z))
    (fun y _hy => by rw [p.actual_fixedMap ε close.1 window.le]; exact close.2.2 y z) hy

omit [FiniteDimensional ℝ E] in
/-- The complete finite filtration, including the fixed absorbing zero level,
has one common noise germ, uniformly over every admissible driving law. -/
theorem Representation.eventually_all_shifted_kernel_support [CompactSpace M]
    (p : Representation F Parameters evaluate) (N : ℕ) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A) (levels : ℕ → Set M) (ℓ : ℕ)
    (compact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i))
    (adapted : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i)))
    (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ L : Laws (ι := ι),
      ∀ i, i ≤ ℓ → ∀ x ∈ shiftedFiltration T N A levels i,
        (NoiseKernel.chain (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
          (p.allScale_measurable ε) Aᶜ hA.measurableSet.compl w hw R hR hwR).killedTransition x
          (shiftedFiltration T N A levels i)ᶜ = 0 := by
  filter_upwards [p.eventually_shifted_kernel_support N A hA.measurableSet levels ℓ
    compact adapted w hw R hR hwR,
    p.eventually_strict_absorbing_support A hA strict w hw R hR hwR] with ε positive zero
  intro L i hi
  by_cases h : i = 0
  · subst i
    simpa only [shiftedFiltration_zero] using zero L
  · exact positive L i (Nat.pos_of_ne_zero h) hi

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
