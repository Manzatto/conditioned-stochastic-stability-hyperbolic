module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureWordIdentity
public import LeanShared.Geometry.ManifoldFiniteLabelledHolderWords
public import LeanShared.Geometry.RealManifoldLocalization
public import LeanShared.Analysis.ActualFiniteWordReindex
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Tactic.Ring

/-! Every actual cutoff-word output of a smooth manifold input belongs to
the exact closed local little Holder core. The cutoff product itself need
only have the finite regularity supplied by the original noisy word. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ActualFiniteRegularWord CylinderPrincipalCoefficient

private theorem amplitude_terminal_product {X Ω I : Type*} (F : Ω → X → X)
    (w : I → X → ℂ) (t h : X → ℂ) (word : List (Ω × I)) (x : X) :
    ActualFiniteLabelledWord.amplitude F w (fun y => t y * h y) word x =
      ActualFiniteLabelledWord.amplitude F w t word x *
        h (orbit (fun z : Ω × I => F z.1) word x) := by
  induction word generalizing x with
  | nil => simp only [ActualFiniteLabelledWord.amplitude, orbit]
  | cons z word ih =>
    rw [ActualFiniteLabelledWord.amplitude, ih, ActualFiniteLabelledWord.amplitude, orbit]
    exact (mul_assoc _ _ _).symm

variable {E M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I]

theorem Maps.capture_word_local_core (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    {g : M → ℝ} {q b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbq : b < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : I → OpenPartialHomeomorph M E)
    (hc : ∀ i, c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (source : ∀ i, v i ⊆ (c i).source)
    (h : M → ℂ) (smoothh : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ h)
    (ε : NNReal) (hp : 0 < ε) (hw : ε ≤ F.window) {N : ℕ}
    (controls : Fin N → cube (ι := ι) ε) (labels : Fin (N + 1) → I) :
    let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
    let supportθ : tsupport θ ⊆ (c (labels 0)).source :=
      (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
        ((d.support (labels 0)).trans (source (labels 0)))
    ∃ output : EuclideanSmoothHolderCore.space
        (ChartLocalization.localSupport_isCompact (c (labels 0)) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1,
      ∀ x, EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact (c (labels 0)) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1 output x =
        ChartLocalization.coordinate (c (labels 0))
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun j : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
            (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            h (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x := by
  classical
  dsimp only
  let e := F.atlas.source
  have cover : (univ : Set M) ⊆ ⋃ i, (e i).source := by
    intro x _
    have inside : x ∈ ⋃ i, F.atlas.patch i := by
      rw [F.atlas.patch_cover]
      exact mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp inside
    exact mem_iUnion.mpr ⟨i, F.atlas.patch_source i (subset_closure hi)⟩
  let D : ConstructedManifoldLocalization.Data e (univ : Set M) :=
    RealManifoldLocalization.data isCompact_univ cover
  let atlas := F.atlas.source_smooth
  let maps : cube (ι := ι) ε → M → M := fun control => F.family ε control.val
  have mapSmooth (control : cube (ι := ι) ε) :
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps control) := F.contMDiff_one hr ε hp hw control
  obtain ⟨u, hbu, hu1, huq, localized⟩ := d.exists_common_localized_order weight hb hb1 hbq
  have weightRegular (i : Option I) :
      FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (captureWeights d g i) := by
    cases i with
    | none => exact FractionalManifoldRegularity.lower_subunit (hb.trans hbu) hu1 huq weight.ofReal
    | some i => exact localized i
  let terminal := captureTerminals d (captureEnd labels)
  have smoothTerminals (j : Option I) :
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (captureTerminals d j) := by
    cases j with
    | none => exact contMDiff_const
    | some j => exact Complex.ofRealCLM.contMDiff.comp (d.smooth j)
  have smoothTerminal : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ terminal := smoothTerminals (captureEnd labels)
  let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
  have supportθ : tsupport θ ⊆ (c (labels 0)).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
      ((d.support (labels 0)).trans (source (labels 0)))
  have smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ :=
    Complex.ofRealCLM.contMDiff.comp (d.smooth (labels 0))
  have smoothProduct : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ, ℂ)) ∞
      (fun z : ℂ × ℂ => z.1 * z.2) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff
  have smoothInput : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (fun m => terminal m * h m) :=
    smoothProduct.comp (smoothTerminal.prodMk_space smoothh)
  let output := ManifoldFiniteLabelledHolderWords.localWord μE e D atlas hb hb1 hbu hu1
    maps mapSmooth (captureWeights d g) weightRegular (fun m => terminal m * h m)
    smoothInput (c (labels 0)) (hc (labels 0)) θ smoothθ
    (HasCompactSupport.of_compactSpace _) supportθ (List.ofFn (captureLetters controls labels))
  refine ⟨output, ?_⟩
  intro x
  dsimp only [output]
  rw [ManifoldFiniteLabelledHolderWords.localWord_physical μE e D atlas hb hb1 hbu hu1
    maps mapSmooth (captureWeights d g) weightRegular (fun m => terminal m * h m)
    smoothInput (c (labels 0)) (hc (labels 0)) θ smoothθ
    (HasCompactSupport.of_compactSpace _) supportθ (List.ofFn (captureLetters controls labels)) x]
  by_cases inside : x ∈ (c (labels 0)).target
  · simp only [ChartLocalization.coordinate, ite_eq_left inside]
    rw [amplitude_terminal_product]
    have actualOrbit (m : M) : orbit (fun z : cube (ι := ι) ε × Option I => maps z.1)
        (List.ofFn (captureLetters controls labels)) m = prefixOrbit maps controls N m := by
      rw [← reindex_orbit_list maps Prod.fst, List.map_ofFn]
      change orbit maps (List.ofFn controls) m = _
      exact orbit_ofFn_eq_prefix maps controls m
    rw [actualOrbit, ← mul_assoc, capture_word_amplitude_identity maps d g controls labels]
    exact mul_assoc _ _ _
  · simp only [ChartLocalization.coordinate, ite_eq_right inside]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
