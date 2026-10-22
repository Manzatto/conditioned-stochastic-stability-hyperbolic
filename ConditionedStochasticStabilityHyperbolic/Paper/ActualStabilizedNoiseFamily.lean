module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoisePoint

/-! One actual positive noise window and one prescribed first-marginal
probability family descend together from the stabilizing product. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseFamily
open LeanShared RegularNoise ActualStabilizedNoisePoint
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] [ChartedSpace E X] [ChartedSpace H Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
  (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := H) (ι := κ) T' r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (V : Set X) (w : X → ℝ) (hw : Measurable w)
  (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX)

local instance stabilizedFamilyCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance stabilizedFamilyCompactCollar : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact
local instance stabilizedFamilyCompactProduct : CompactSpace (closure (Set.prod V (univ : Set Y))) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- No new quasi-ergodic measures are chosen: the family and its limit are
both the prescribed first marginals. The window precedes starting states
and observables, as required by the original local existence statement. -/
theorem existence_and_limit
    (nonnegative : ∀ x, 0 ≤ w x) (Λ : Set X) (hΛ : (closure V ∩ Λ).Nonempty)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδwindow : δ ≤ min P.window Q.window)
    (νY : ℝ≥0 → ProbabilityMeasure (univ : Set Y))
    (ν : ℝ≥0 → ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (ν₀ : ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (limit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀))
    (sf : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      HasStrongFellerKernel (original P Q L ε hε (hεδ.trans hδwindow) V w hw RX hRX bound))
    (auxiliary : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (auxiliaryLocal P Q L' ε hε (hεδ.trans hδwindow) RY hRY) univ (νY ε))
    (localPoint : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.Point
        (closedProduct P Q L L' ε hε (hεδ.trans hδwindow) V w hw RX RY hRX hRY bound)
        (RX * RY) {z | z.val.1 ∈ Λ} (ν ε))
    (localGap : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (closedProduct P Q L L' ε hε (hεδ.trans hδwindow) V w hw RX RY hRX hRY bound)
        {z | z.val.1 ∈ Λ} (ν ε)) (y : Y) :
    LocalConclusions.Existence P L (closure V) Λ isClosed_closure.measurableSet
      (fun x => w x.val) (hw.comp measurable_subtype_coe) RX hRX (fun x => bound x.val) ∧
    Tendsto (fun ε => (ν ε).map (fun z => ((LiveProductCoordinates.closedCollar V) z).1))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (ν₀.map (fun z => ((LiveProductCoordinates.closedCollar V) z).1))) ∧
    ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.Point
        (original P Q L ε hε (hεδ.trans hδwindow) V w hw RX hRX bound)
        RX {x | x.val ∈ Λ}
        ((ν ε).map (fun z => ((LiveProductCoordinates.closedCollar V) z).1)) := by
  constructor
  · refine ⟨δ, hδwindow.trans (min_le_left _ _), hδ,
      (fun ε => (ν ε).map (fun z => ((LiveProductCoordinates.closedCollar V) z).1)), ?_⟩
    intro ε hε hεδ
    exact ActualStabilizedNoisePoint.point P Q L L' ε hε (hεδ.trans hδwindow)
      V w hw RX RY hRX hRY bound nonnegative Λ hΛ (sf ε hε hεδ)
      (νY ε) (auxiliary ε hε hεδ) (ν ε) (localPoint ε hε hεδ) (localGap ε hε hεδ) y
  · constructor
    · exact ReindexedProductLocalFamily.tendsto_marginal
        (LiveProductCoordinates.closedCollar V).symm _ ν ν₀ limit
    · intro ε hε hεδ
      exact ActualStabilizedNoisePoint.point P Q L L' ε hε (hεδ.trans hδwindow)
        V w hw RX RY hRX hRY bound nonnegative Λ hΛ (sf ε hε hεδ)
        (νY ε) (auxiliary ε hε hεδ) (ν ε) (localPoint ε hε hεδ) (localGap ε hε hεδ) y

end ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseFamily
