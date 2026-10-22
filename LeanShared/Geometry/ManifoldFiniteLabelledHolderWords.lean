module
public import LeanShared.Geometry.ManifoldClosedCutoffHolderLocalization
public import LeanShared.Geometry.ManifoldWeightedHolderOperator
public import LeanShared.Analysis.ActualFiniteLabelledWord

/-! Every literal labelled weighted word has a constructed global ordinary
little Holder vector and a local vector on any prescribed genuine chart's
exact closed cutoff support. This constructs local range membership for
finite-regular words; neither a word representation nor membership is input. -/
@[expose] public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldFiniteLabelledHolderWords
open FiniteBlockAnnealedEstimates
variable {E M J Ω I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  (e : J → OpenPartialHomeomorph M E) (D : ConstructedManifoldLocalization.Data e (univ : Set M))
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {b u : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbu : b < u) (hu1 : u < 1)
  (maps : Ω → M → M) (mapSmooth : ∀ a, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps a))
  (weights : I → M → ℂ)
  (weightRegular : ∀ i, FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (weights i))

abbrev Global := ManifoldSmoothHolderCore.Lower e D isOpen_univ hb hb1
local instance globalNormed : NormedAddCommGroup (Global e D hb hb1) := inferInstance
local instance globalSemi : SeminormedAddCommGroup (Global e D hb hb1) :=
  (globalNormed e D hb hb1).toSeminormedAddCommGroup
local instance globalScalar : NormedSpace ℂ (Global e D hb hb1) := inferInstance

def generator (z : Ω × I) : Global e D hb hb1 →L[ℂ] Global e D hb hb1 :=
  ManifoldWeightedHolderOperator.operator μ e D atlas isOpen_univ Subset.rfl hb hb1 hbu hu1
    (weightRegular z.2) (subset_univ _) (maps z.1) (mapSmooth z.1)

variable (terminal : M → ℂ)
  (terminalSmooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ terminal)

def terminalCore : SmoothSupportedManifoldCore.core (E := E) (univ : Set M) :=
  ⟨terminal, terminalSmooth, subset_univ _⟩

def wordVector (word : List (Ω × I)) : Global e D hb hb1 :=
  listWord (generator μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular) word
    (ManifoldSmoothHolderCore.smooth e D atlas isOpen_univ hb hb1 (terminalCore terminal terminalSmooth))

omit [CompactSpace M] in
theorem wordVector_physical (word : List (Ω × I)) (x : M) :
    ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1
      (wordVector μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
        terminal terminalSmooth word) x =
      ActualFiniteLabelledWord.amplitude maps weights terminal word x := by
  let Q := generator μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
  let v := ManifoldSmoothHolderCore.smooth e D atlas isOpen_univ hb hb1
    (terminalCore terminal terminalSmooth)
  have action (z : Ω × I) f y :
      ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1 (Q z f) y =
        weights z.2 y * ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1 f (maps z.1 y) :=
    ManifoldWeightedHolderOperator.physical_operator μ e D atlas isOpen_univ Subset.rfl
      hb hb1 hbu hu1 (weightRegular z.2) (subset_univ _) (maps z.1) (mapSmooth z.1) f y
  have terminalPhysical : (fun y => ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1 v y) = terminal := by
    funext y
    exact ManifoldSmoothHolderCore.physical_smooth e D atlas isOpen_univ hb hb1
      Subset.rfl (terminalCore terminal terminalSmooth) y
  have h := ActualFiniteLabelledWord.physical_word maps weights
    (fun f y => ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1 f y) Q action v word x
  change ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1 (listWord Q word v) x = _
  exact h.trans (congrArg (fun t : M → ℂ => ActualFiniteLabelledWord.amplitude maps weights t word x)
    terminalPhysical)

variable (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source)

def localWord (word : List (Ω × I)) : EuclideanSmoothHolderCore.space
    (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1 :=
  ManifoldClosedCutoffHolderLocalization.localization e D atlas isOpen_univ hb hb1
    c hc θ smoothθ compactθ supportθ
    (wordVector μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
      terminal terminalSmooth word)

omit [CompactSpace M] in
theorem localWord_physical (word : List (Ω × I)) (y : E) :
    EuclideanSmoothHolderCore.physical
      (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).closure hb hb1
      (localWord μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
        terminal terminalSmooth c hc θ smoothθ compactθ supportθ word) y =
      ChartLocalization.coordinate c θ (ActualFiniteLabelledWord.amplitude maps weights terminal word) y := by
  rw [localWord, ManifoldClosedCutoffHolderLocalization.physical_localization
    e D atlas isOpen_univ hb hb1 c hc θ smoothθ compactθ supportθ Subset.rfl]
  have identity : (ManifoldSmoothHolderCore.physical e D isOpen_univ hb hb1
      (wordVector μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
        terminal terminalSmooth word) : M → ℂ) =
      ActualFiniteLabelledWord.amplitude maps weights terminal word := by
    funext x
    exact wordVector_physical μ e D atlas hb hb1 hbu hu1 maps mapSmooth weights weightRegular
      terminal terminalSmooth word x
  rw [identity]

end LeanShared.ManifoldFiniteLabelledHolderWords
