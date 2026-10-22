module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformWeightedHolderBound
public import LeanShared.Geometry.ManifoldHolderCutoffLocalization
public import LeanShared.Geometry.RealManifoldLocalization
public import LeanShared.Analysis.ActualFiniteLabelledWord
import all LeanShared.Analysis.FiniteBlockAnnealedEstimates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! A finite family of literal weights has one common small-noise window
and exponential bound for every labelled word and every smooth terminal
cutoff. The ordinary space is constructed on the whole compact manifold.
The original model is only normed; no Euclidean metric is imposed on it. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared FiniteBlockAnnealedEstimates
variable {E M ι I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I] [Fintype J]

theorem Maps.finite_labelled_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {a u : ℝ} (ha : 0 < a) (ha1 : a < 1) (hau : a < u) (hu1 : u < 1)
    (weights : I → M → ℂ)
    (weightRegular : ∀ i, FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (weights i))
    (terminal : J → M → ℂ)
    (terminalSmooth : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (terminal j))
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
    (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ word : List (cube (ι := ι) ε × I),
      ∀ j : J, ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate c θ
          (ActualFiniteLabelledWord.amplitude
            (fun control : cube (ι := ι) ε => F.family ε control.val)
            weights (terminal j) word) x) ∧
        ‖f‖ ≤ C * B ^ word.length ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport c θ ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ word.length) * dist x y ^ a := by
  classical
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
  have region : (univ : Set M) ⊆ univ := Subset.rfl
  have support (i : I) : tsupport (weights i) ⊆ (univ : Set M) := subset_univ _
  have individual (i : I) := F.exists_uniform_holder_operator_bound μE e D atlas
    isOpen_univ region ha ha1 hau hu1 (weightRegular i) (support i) hr regular
  choose radius positive constant nonnegative bound using individual
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
  have below : η ≤ F.window := Finset.inf'_le windows (Finset.mem_univ none)
  have belowEach (i : I) : η ≤ radius i :=
    Finset.inf'_le windows (Finset.mem_univ (some i))
  let B : ℝ := ∑ i, constant i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => nonnegative i
  have constantBound (i : I) : constant i ≤ B :=
    Finset.single_le_sum (fun k _ => nonnegative k) (Finset.mem_univ i)
  let loc := ManifoldHolderCutoffLocalization.localization e D atlas (V := univ)
    isOpen_univ ha ha1 c hc θ smoothθ compactθ supportθ
  let terminalCore (j : J) : SmoothSupportedManifoldCore.core (E := E) (univ : Set M) :=
    ⟨terminal j, terminalSmooth j, subset_univ _⟩
  let terminalVector (j : J) := ManifoldSmoothHolderCore.smooth e D atlas
    (V := univ) isOpen_univ ha ha1 (terminalCore j)
  let terminalBound : ℝ := ∑ j, ‖terminalVector j‖
  have hTerminalBound : 0 ≤ terminalBound := Finset.sum_nonneg fun j _ => norm_nonneg _
  have terminalNorm (j : J) : ‖terminalVector j‖ ≤ terminalBound :=
    Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)
  let C : ℝ := ‖loc‖ * terminalBound
  refine ⟨η, positiveη, below, B, C, hB, mul_nonneg (norm_nonneg loc) hTerminalBound, ?_⟩
  intro ε hp hw word j
  let maps : cube (ι := ι) ε → M → M := fun control => F.family ε control.val
  let Q := fun z : cube (ι := ι) ε × I => ManifoldWeightedHolderOperator.operator
    μE e D atlas isOpen_univ region ha ha1 hau hu1 (weightRegular z.2) (support z.2)
    (maps z.1) (F.contMDiff_one hr ε hp (hw.trans below) z.1)
  have normQ (z : cube (ι := ι) ε × I) : ‖Q z‖ ≤ B :=
    (bound z.2 ε hp (hw.trans (belowEach z.2)) (hw.trans below) z.1).trans (constantBound z.2)
  let result := listWord Q word (terminalVector j)
  have normResult : ‖result‖ ≤ B ^ word.length * terminalBound :=
    (strong_word_bound Q B hB normQ word (terminalVector j)).trans
      (mul_le_mul_of_nonneg_left (terminalNorm j) (pow_nonneg hB _))
  have terminalPhysical (x : M) :
      ManifoldSmoothHolderCore.physical e D isOpen_univ ha ha1 (terminalVector j) x = terminal j x :=
    ManifoldSmoothHolderCore.physical_smooth e D atlas isOpen_univ ha ha1 region (terminalCore j) x
  have physicalWord (x : M) : ManifoldSmoothHolderCore.physical e D isOpen_univ ha ha1 result x =
      ActualFiniteLabelledWord.amplitude maps weights (terminal j) word x := by
    have action (z : cube (ι := ι) ε × I) v y :
        ManifoldSmoothHolderCore.physical e D isOpen_univ ha ha1 (Q z v) y =
          weights z.2 y * ManifoldSmoothHolderCore.physical e D isOpen_univ ha ha1 v (maps z.1 y) :=
      ManifoldWeightedHolderOperator.physical_operator μE e D atlas isOpen_univ region
        ha ha1 hau hu1 (weightRegular z.2) (support z.2) (maps z.1)
        (F.contMDiff_one hr ε hp (hw.trans below) z.1) v y
    have h := ActualFiniteLabelledWord.physical_word maps weights
      (fun v y => ManifoldSmoothHolderCore.physical e D isOpen_univ ha ha1 v y)
      Q action (terminalVector j) word x
    simpa only [funext terminalPhysical] using h
  have formula (x : E) : BoundedHolderSpace.physical E a (loc result) x =
      ChartLocalization.coordinate c θ
        (ActualFiniteLabelledWord.amplitude maps weights (terminal j) word) x := by
    rw [ManifoldHolderCutoffLocalization.physical_localization]
    exact congrArg (fun h : M → ℂ => ChartLocalization.coordinate c θ h x) (funext physicalWord)
  have graphBound : ‖loc result‖ ≤ C * B ^ word.length :=
    (loc.le_opNorm result).trans ((mul_le_mul_of_nonneg_left normResult (norm_nonneg loc)).trans_eq
      (by dsimp [C]; ring))
  refine ⟨BoundedHolderSpace.physical E a (loc result), formula,
    (BoundedHolderSpace.physical_norm_le E a (loc result)).trans graphBound, ?_, ?_⟩
  · apply closure_minimal _ (ChartLocalization.localSupport_isCompact c θ supportθ compactθ).isClosed
    intro x hx
    by_contra outside
    exact hx ((formula x).trans (ChartLocalization.coordinate_zero_outside c θ
      (ActualFiniteLabelledWord.amplitude maps weights (terminal j) word) x outside))
  · intro x y
    exact (BoundedHolderSpace.increment_bound E a (loc result) x y).trans
      (mul_le_mul_of_nonneg_right graphBound (Real.rpow_nonneg dist_nonneg _))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
