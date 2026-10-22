module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeAmplitudeHolder
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseTerminalWordIdentity

/-! Uniform Holder bounds for the full literal cutoff-word amplitude
multiplied by an auxiliary terminal cutoff at the word endpoint. The
terminal slot is an independent finite index: the complete beta word,
including its terminal beta, is retained, and the auxiliary factor is
added through the arbitrary smooth terminal family of the labelled-word
estimate. One window and one pair of exponential constants serve every
word length, control, label word and terminal slot. The same bound is
transported to the genuine Fourier model and to the adapted tube charts. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff BoundedContinuousFunction NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared CylinderPrincipalCoefficient

section Capture
variable {E Z M ι I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I] [Fintype J]

theorem Maps.capture_labelled_terminal_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j))
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
    (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ word : List (cube (ι := ι) ε × Option I),
      ∀ k : Option I, ∀ j : J, ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate c θ
          (ActualFiniteLabelledWord.amplitude
            (fun control : cube (ι := ι) ε => F.family ε control.val)
            (captureWeights d g) (fun m => captureTerminals d k m * τ j m) word) x) ∧
        ‖f‖ ≤ C * B ^ word.length ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport c θ ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ word.length) * dist x y ^ a := by
  obtain ⟨u, hau, hu1, huq, localized⟩ := d.exists_common_localized_order weight ha ha1 haq
  have weightRegular (i : Option I) :
      FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (captureWeights d g i) := by
    cases i with
    | none => exact FractionalManifoldRegularity.lower_subunit (ha.trans hau) hu1 huq weight.ofReal
    | some i => exact localized i
  have captureSmooth (k : Option I) :
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (captureTerminals d k) := by
    cases k with
    | none => exact contMDiff_const
    | some k => exact Complex.ofRealCLM.contMDiff.comp (d.smooth k)
  have terminalSmooth (kj : Option I × J) :
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (fun m => captureTerminals d kj.1 m * τ kj.2 m) :=
    contDiff_mul.contMDiff.comp ((captureSmooth kj.1).prodMk_space (smoothτ kj.2))
  obtain ⟨η, positive, below, B, C, nonnegB, nonnegC, estimates⟩ :=
    F.finite_labelled_amplitude_holder (J := Option I × J) μE hr regular ha ha1 hau hu1
      (captureWeights d g) weightRegular (fun kj m => captureTerminals d kj.1 m * τ kj.2 m)
      terminalSmooth c hc θ smoothθ compactθ supportθ
  exact ⟨η, positive, below, B, C, nonnegB, nonnegC,
    fun ε hp hw word k j => estimates ε hp hw word (k, j)⟩

theorem Maps.capture_word_terminal_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j))
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I, ∀ j : J,
      ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (c (labels 0))
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆
          ChartLocalization.localSupport (c (labels 0)) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  classical
  have support (i : I) : tsupport (fun m => (d.beta i m : ℂ)) ⊆ (c i).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta i)).trans ((d.support i).trans (source i))
  have individual (i : I) := F.capture_labelled_terminal_amplitude_holder μE hr regular ha ha1 haq
    weight d τ smoothτ (c i) (hc i) (fun m => (d.beta i m : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (d.smooth i)) (HasCompactSupport.of_compactSpace _) (support i)
  choose radius positive below B C hB hC estimates using individual
  let windows : Option I → NNReal := fun k => match k with
    | none => F.window
    | some i => radius i
  let η : NNReal := Finset.univ.inf' Finset.univ_nonempty windows
  have positiveη : 0 < η := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro k _
    cases k with
    | none => exact F.window_positive
    | some i => exact positive i
  have belowOuter : η ≤ F.window := Finset.inf'_le windows (Finset.mem_univ none)
  have belowEach (i : I) : η ≤ radius i :=
    Finset.inf'_le windows (Finset.mem_univ (some i))
  let commonB : ℝ := ∑ i, B i
  let commonC : ℝ := ∑ i, C i
  have nonnegB : 0 ≤ commonB := Finset.sum_nonneg fun i _ => hB i
  have nonnegC : 0 ≤ commonC := Finset.sum_nonneg fun i _ => hC i
  have boundB (i : I) : B i ≤ commonB :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)
  have boundC (i : I) : C i ≤ commonC :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)
  refine ⟨η, positiveη, belowOuter, commonB, commonC, nonnegB, nonnegC, ?_⟩
  intro ε hp hw N controls labels j
  let i := labels 0
  let maps : cube (ι := ι) ε → M → M := fun control => F.family ε control.val
  obtain ⟨f, formula, normBound, supportBound, holder⟩ := estimates i ε hp
    (hw.trans (belowEach i)) (List.ofFn (captureLetters controls labels)) (captureEnd labels) j
  have commonBound : C i * B i ^ N ≤ commonC * commonB ^ N :=
    mul_le_mul (boundC i) (pow_le_pow_left₀ (hB i) (boundB i) N)
      (pow_nonneg (hB i) N) nonnegC
  refine ⟨f, ?_, ?_, supportBound, ?_⟩
  · intro y
    rw [formula]
    change _ = ChartLocalization.coordinate (c i) _ _ y
    by_cases inside : y ∈ (c i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left inside]
      rw [capture_terminal_word_amplitude_identity maps d g (fun _ => τ j) controls labels i
        ((c i).symm y), mul_assoc]
    · simp only [ChartLocalization.coordinate, ite_eq_right inside]
  · have normBound' : ‖f‖ ≤ C i * B i ^ N := by
      simpa only [List.length_ofFn] using normBound
    exact normBound'.trans commonBound
  · intro x y
    have holder' : ‖f x - f y‖ ≤ (C i * B i ^ N) * dist x y ^ a := by
      simpa only [List.length_ofFn] using holder x y
    exact holder'.trans
      (mul_le_mul_of_nonneg_right commonBound (Real.rpow_nonneg dist_nonneg _))

theorem Maps.recharted_capture_word_terminal_amplitude_holder (μE : Measure E)
    [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j))
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source) (e : E ≃L[ℝ] Z) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I, ∀ j : J,
      ∃ f : Z →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate
          (LinearRechartedManifold.chartImage e (c (labels 0)))
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (LinearRechartedManifold.chartImage e (c (labels 0))) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  obtain ⟨η, positive, below, B, C, nonnegB, nonnegC, estimates⟩ :=
    F.capture_word_terminal_amplitude_holder μE hr regular ha ha1 haq weight d τ smoothτ c hc source
  let L : ℝ := ‖e.symm.toContinuousLinearMap‖
  let factor : ℝ := max 1 (L ^ a)
  have oneFactor : 1 ≤ factor := le_max_left _ _
  have rpowFactor : L ^ a ≤ factor := le_max_right _ _
  have nonnegFactor : 0 ≤ factor := zero_le_one.trans oneFactor
  refine ⟨η, positive, below, B, C * factor, nonnegB, mul_nonneg nonnegC nonnegFactor, ?_⟩
  intro ε hp hw N controls labels j
  obtain ⟨f, formula, normBound, support, holder⟩ := estimates ε hp hw N controls labels j
  let f' : Z →ᵇ ℂ := f.compContinuous ⟨e.symm, e.symm.continuous⟩
  have coefficient : C * B ^ N ≤ (C * factor) * B ^ N := by
    calc
      _ = (C * 1) * B ^ N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left oneFactor nonnegC)
        (pow_nonneg nonnegB _)
  refine ⟨f', ?_, (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
    (normBound.trans coefficient), ?_, ?_⟩
  · intro x
    exact (formula (e.symm x)).trans
      (ConstructedManifoldLocalization.coordinate_linearRechart c e (labels 0) _ _ x).symm
  · rw [ConstructedManifoldLocalization.localSupport_linearRechart c e]
    change tsupport ((fun x => f x) ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro x hx
    exact ⟨e.symm x, support hx, e.apply_symm_apply x⟩
  · intro x y
    have distance : dist (e.symm x) (e.symm y) ≤ L * dist x y :=
      e.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul x y
    have compose := (holder (e.symm x) (e.symm y)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg distance ha.le)
        (mul_nonneg nonnegC (pow_nonneg nonnegB _)))
    rw [Real.mul_rpow (norm_nonneg _) dist_nonneg] at compose
    change ‖f (e.symm x) - f (e.symm y)‖ ≤ _
    calc
      _ ≤ (C * B ^ N) * (L ^ a * dist x y ^ a) := compose
      _ ≤ (C * B ^ N) * (factor * dist x y ^ a) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right rpowFactor (Real.rpow_nonneg dist_nonneg _))
          (mul_nonneg nonnegC (pow_nonneg nonnegB _))
      _ = _ := by ring

end Capture

section Tube
open HyperbolicBasicSet HyperbolicAdaptedPatchSystem
variable {E M ι J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] [Fintype ι] [Fintype J]

theorem Maps.adapted_tube_terminal_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j)) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → s, ∀ j : J,
      ∃ f : system.EuclideanModel →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (atlas.normalizedTubeChart (labels 0).val)
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (atlas.normalizedTubeChart (labels 0).val) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  let e := atlas.originalModelEquiv
  let c : s → OpenPartialHomeomorph M E := fun i => atlas.originalTubeChart e i.val
  have charts (i : s) : c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M :=
    atlas.originalTubeChart_mem_maximal e i.val
  have source (i : s) : atlas.normalizedTube radius i.val ⊆ (c i).source := by
    intro x hx
    exact hx.1
  have estimates := F.recharted_capture_word_terminal_amplitude_holder μE hr regular ha ha1 haq
    weight d τ smoothτ c charts source e
  simpa only [c, ChartAtlas.originalTubeChart_chartImage] using estimates

end Tube

section SourceCapture
variable {E Z M ι I J Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I] [Fintype J] [Fintype Q]

/-- Both a source cutoff `χ k` (for instance a pressure-center cutoff) and an
independent auxiliary terminal cutoff `τ j` multiply the literal beta word. -/
theorem Maps.source_terminal_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source)
    (χ : Q → M → ℂ) (smoothχ : ∀ k, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (χ k))
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j)) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I, ∀ k : Q, ∀ j : J,
      ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (c (labels 0))
          (fun m => χ k m * (FiniteSmoothCapturePartition.wordCutoff d
            (fun l : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls l.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆
          ChartLocalization.localSupport (c (labels 0)) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  classical
  have support (i : I) : tsupport (fun m => (d.beta i m : ℂ)) ⊆ (c i).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta i)).trans ((d.support i).trans (source i))
  have multiply : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ,ℂ)) ∞
      (fun z : ℂ × ℂ => z.1 * z.2) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff
  have supportProduct (p : I × Q) :
      tsupport (fun m => χ p.2 m * (d.beta p.1 m : ℂ)) ⊆ (c p.1).source :=
    tsupport_mul_subset_right.trans (support p.1)
  have individual (p : I × Q) := F.capture_labelled_terminal_amplitude_holder μE hr regular ha ha1 haq
    weight d τ smoothτ (c p.1) (hc p.1) (fun m => χ p.2 m * (d.beta p.1 m : ℂ))
    (multiply.comp ((smoothχ p.2).prodMk_space (Complex.ofRealCLM.contMDiff.comp (d.smooth p.1))))
    (HasCompactSupport.of_compactSpace _) (supportProduct p)
  choose radius positive below B C hB hC estimates using individual
  let windows : Option (I × Q) → NNReal := fun k => match k with
    | none => F.window
    | some i => radius i
  let η : NNReal := Finset.univ.inf' Finset.univ_nonempty windows
  have positiveη : 0 < η := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro k _
    cases k with
    | none => exact F.window_positive
    | some i => exact positive i
  have belowOuter : η ≤ F.window := Finset.inf'_le windows (Finset.mem_univ none)
  have belowEach (i : I × Q) : η ≤ radius i :=
    Finset.inf'_le windows (Finset.mem_univ (some i))
  let commonB : ℝ := ∑ i, B i
  let commonC : ℝ := ∑ i, C i
  have nonnegB : 0 ≤ commonB := Finset.sum_nonneg fun i _ => hB i
  have nonnegC : 0 ≤ commonC := Finset.sum_nonneg fun i _ => hC i
  have boundB (i : I × Q) : B i ≤ commonB :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)
  have boundC (i : I × Q) : C i ≤ commonC :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)
  refine ⟨η, positiveη, belowOuter, commonB, commonC, nonnegB, nonnegC, ?_⟩
  intro ε hp hw N controls labels k j
  let i := labels 0
  let p : I × Q := (i, k)
  let maps : cube (ι := ι) ε → M → M := fun control => F.family ε control.val
  obtain ⟨f, formula, normBound, supportBound, holder⟩ := estimates p ε hp
    (hw.trans (belowEach p)) (List.ofFn (captureLetters controls labels)) (captureEnd labels) j
  dsimp only [p] at formula
  have commonBound : C p * B p ^ N ≤ commonC * commonB ^ N :=
    mul_le_mul (boundC p) (pow_le_pow_left₀ (hB p) (boundB p) N)
      (pow_nonneg (hB p) N) nonnegC
  refine ⟨f, ?_, ?_, supportBound.trans (image_mono tsupport_mul_subset_right), ?_⟩
  · intro y
    rw [formula]
    change _ = ChartLocalization.coordinate (c i) _ _ y
    by_cases inside : y ∈ (c i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left inside]
      have literal := capture_terminal_word_amplitude_identity maps d g (fun _ => τ j) controls
        labels i ((c i).symm y)
      rw [mul_assoc, literal]
      ring
    · simp only [ChartLocalization.coordinate, ite_eq_right inside]
  · have normBound' : ‖f‖ ≤ C p * B p ^ N := by
      simpa only [List.length_ofFn] using normBound
    exact normBound'.trans commonBound
  · intro x y
    have holder' : ‖f x - f y‖ ≤ (C p * B p ^ N) * dist x y ^ a := by
      simpa only [List.length_ofFn] using holder x y
    exact holder'.trans
      (mul_le_mul_of_nonneg_right commonBound (Real.rpow_nonneg dist_nonneg _))

theorem Maps.recharted_source_terminal_amplitude_holder (μE : Measure E)
    [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j))
    (χ : Q → M → ℂ) (smoothχ : ∀ k, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (χ k)) (e : E ≃L[ℝ] Z) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → I, ∀ k : Q, ∀ j : J,
      ∃ f : Z →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate
          (LinearRechartedManifold.chartImage e (c (labels 0)))
          (fun m => χ k m * (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (LinearRechartedManifold.chartImage e (c (labels 0))) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  obtain ⟨η, positive, below, B, C, nonnegB, nonnegC, estimates⟩ :=
    F.source_terminal_amplitude_holder μE hr regular ha ha1 haq weight d c hc source χ smoothχ τ smoothτ
  let L : ℝ := ‖e.symm.toContinuousLinearMap‖
  let factor : ℝ := max 1 (L ^ a)
  have oneFactor : 1 ≤ factor := le_max_left _ _
  have rpowFactor : L ^ a ≤ factor := le_max_right _ _
  have nonnegFactor : 0 ≤ factor := zero_le_one.trans oneFactor
  refine ⟨η, positive, below, B, C * factor, nonnegB, mul_nonneg nonnegC nonnegFactor, ?_⟩
  intro ε hp hw N controls labels k j
  obtain ⟨f, formula, normBound, support, holder⟩ := estimates ε hp hw N controls labels k j
  let f' : Z →ᵇ ℂ := f.compContinuous ⟨e.symm, e.symm.continuous⟩
  have coefficient : C * B ^ N ≤ (C * factor) * B ^ N := by
    calc
      _ = (C * 1) * B ^ N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left oneFactor nonnegC)
        (pow_nonneg nonnegB _)
  refine ⟨f', ?_, (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
    (normBound.trans coefficient), ?_, ?_⟩
  · intro x
    exact (formula (e.symm x)).trans
      (ConstructedManifoldLocalization.coordinate_linearRechart c e (labels 0) _ _ x).symm
  · rw [ConstructedManifoldLocalization.localSupport_linearRechart c e]
    change tsupport ((fun x => f x) ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro x hx
    exact ⟨e.symm x, support hx, e.apply_symm_apply x⟩
  · intro x y
    have distance : dist (e.symm x) (e.symm y) ≤ L * dist x y :=
      e.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul x y
    have compose := (holder (e.symm x) (e.symm y)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg distance ha.le)
        (mul_nonneg nonnegC (pow_nonneg nonnegB _)))
    rw [Real.mul_rpow (norm_nonneg _) dist_nonneg] at compose
    change ‖f (e.symm x) - f (e.symm y)‖ ≤ _
    calc
      _ ≤ (C * B ^ N) * (L ^ a * dist x y ^ a) := compose
      _ ≤ (C * B ^ N) * (factor * dist x y ^ a) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right rpowFactor (Real.rpow_nonneg dist_nonneg _))
          (mul_nonneg nonnegC (pow_nonneg nonnegB _))
      _ = _ := by ring

end SourceCapture

section SourceTube
open HyperbolicBasicSet HyperbolicAdaptedPatchSystem
variable {E M ι J Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] [Fintype ι] [Fintype J] [Fintype Q]

theorem Maps.adapted_tube_source_terminal_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (τ : J → M → ℂ) (smoothτ : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (τ j))
    (χ : Q → M → ℂ) (smoothχ : ∀ k, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (χ k)) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → s, ∀ k : Q, ∀ j : J,
      ∃ f : system.EuclideanModel →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (atlas.normalizedTubeChart (labels 0).val)
          (fun m => χ k m * (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
              (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            τ j (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (atlas.normalizedTubeChart (labels 0).val) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  let e := atlas.originalModelEquiv
  let c : s → OpenPartialHomeomorph M E := fun i => atlas.originalTubeChart e i.val
  have charts (i : s) : c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M :=
    atlas.originalTubeChart_mem_maximal e i.val
  have source (i : s) : atlas.normalizedTube radius i.val ⊆ (c i).source := by
    intro x hx
    exact hx.1
  have estimates := F.recharted_source_terminal_amplitude_holder μE hr regular ha ha1 haq
    weight d c charts source τ smoothτ χ smoothχ e
  simpa only [c, ChartAtlas.originalTubeChart_chartImage] using estimates

end SourceTube

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
