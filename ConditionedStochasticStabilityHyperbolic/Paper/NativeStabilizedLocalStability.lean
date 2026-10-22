module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcome
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalPointCongruence
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseStability
public import ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapRenormalization
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLiveStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductControlGeometry
public import LeanShared.Dynamics.ProductIsolationMixing

/-! Auxiliary and product gaps come from native local outcomes (literal
stability and retention). Only ordinary source records, literal noise identities and
the ordinary deterministic product variational theorem occur as hypotheses. -/
public noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalStability
open LeanShared RegularNoise NativeLocalOutcome
universe uX uY
variable {X : Type uX} {Y : Type uY} {E F H UY UP AY AP IY IP ΩY ΩP : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup UY] [NormedSpace ℝ UY] [FiniteDimensional ℝ UY]
  [MeasurableSpace UY] [BorelSpace UY]
  [NormedAddCommGroup UP] [NormedSpace ℝ UP] [FiniteDimensional ℝ UP]
  [MeasurableSpace UP] [BorelSpace UP]
  [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X] [CompactSpace X]
  [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y] [CompactSpace Y]
  [ChartedSpace H (X × Y)] [IsManifold (𝓘(ℝ, H)) ∞ (X × Y)]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, H)) z)]
  [MetricSpace ΩY] [MetricSpace ΩP]
  {RY : IY → Type*} [∀i,NormedAddCommGroup (RY i)]
  [∀i,NormedSpace ℂ (RY i)] [∀i,CompleteSpace (RY i)]
  {RP : IP → Type*} [∀i,NormedAddCommGroup (RP i)]
  [∀i,NormedSpace ℂ (RP i)] [∀i,CompleteSpace (RP i)]
  {μY : Measure UY} [μY.IsAddHaarMeasure] {μP : Measure UP} [μP.IsAddHaarMeasure]
  {ι κ OY OP : Type*} [Fintype ι] [Fintype κ] [Fintype OY] [Fintype OP]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {Λ V : Set X} {g : X → ℝ}
  (h : HL (E := E) T g Λ V)
  (a : HL (E := F) S (fun _ => 1) univ univ)

local instance canonicalStabilizedCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance canonicalStabilizedCompactProduct : CompactSpace (closure (V ×ˢ (univ : Set Y))) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact
local instance canonicalStabilizedCompactCollar : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
include a in
private theorem auxiliaryCore : isolatedCore S (univ : Set Y) = univ := by
  simpa only [closure_univ] using a.actual_isolated_core.symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace X] [CompactSpace Y] in
include h a in
private theorem productCore :
    isolatedCore (T.prodCongr S) (closure (V ×ˢ (univ : Set Y))) = Λ ×ˢ univ := by
  rw [closure_prod_eq, isolatedCore_product, ← h.actual_isolated_core,
    ← a.actual_isolated_core]

omit [FiniteDimensional ℝ E] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace X] [CompactSpace Y] in
include h in
private theorem productCoreSubset : Λ ×ˢ (univ : Set Y) ⊆ closure (V ×ˢ univ) := by
  rw [closure_prod_eq, closure_univ]
  exact Set.prod_mono (h.basic.subset_neighborhood.trans subset_closure) subset_rfl

variable {SY : Set Y} {VP SP : Set (X × Y)} {gp : X × Y → ℝ}
  (hp : HL (E := H) (T.prodCongr S) gp (Λ ×ˢ univ) VP)
  (σY : Measure Y) [IsFiniteMeasure σY] [σY.IsOpenPosMeasure]
  (σP : Measure (X × Y)) [IsFiniteMeasure σP] [σP.IsOpenPosMeasure]
  (w : X → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (φP : X × Y → ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology X] in
include h hw0 in
/-- The source records are ordinary; both local probability families and both
gaps are constructed inside this proof. The auxiliary normalization is changed
to one without changing its probability. The product scale is then exactly
the original scale, so no mismatched product normalizers are assumed. -/
theorem stability
  (auxiliary : NativeLocalOutcome (E := F) a κ univ isCompact_univ (fun _ => 1) (fun _ => 0))
  (product : NativeLocalOutcome (E := H) hp (ι ⊕ κ) (closure (V ×ˢ univ))
    isClosed_closure.isCompact (fun z => w z.val.1) φP)
  (P : Maps (E := E) (ι := ι) T a.r) (L : Laws (ι := ι))

    (bound : ∀ x, w x ≤ product.scale)
    (maps_match : ∀ ε, product.maps.family ε = independentFamily P auxiliary.maps ε)
    (laws_match : ∀ ε, product.laws.law ε = (productLaws L auxiliary.laws).law ε)
    (smoothSource : ∀ ε (_hε : 0 < ε) (_hwindow : ε ≤ P.window),
      ∀ q : Control (ι := ι) → ℝ, HasCompactSupport q → ContDiff ℝ ∞ q →
        ∀ f : X → ℝ, Measurable f → (∃ C ≥ 0, ∀x, ‖f x‖ ≤ C) →
          Continuous (fun x => ∫ z : cube (ι := ι) ε,
            q z.val * f (P.family ε z.val x) ∂cubeVolume ε))
    (potential : X → ℝ) (νeq : ProbabilityMeasure X)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T potential Λ νeq)
    (unique : ∀ ζ : ProbabilityMeasure X,
      ThermodynamicDefinitions.IsEquilibriumState T potential Λ ζ → ζ = νeq)
    (productVariational : ∀ ζ : ProbabilityMeasure Y,
      ThermodynamicDefinitions.IsEquilibriumState S
        (fun y => (0 : ℝ) - Real.log (a.basic.hyperbolic.unstableJacobian y)) univ ζ →
      ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S)
        (fun z => φP z - Real.log (hp.basic.hyperbolic.unstableJacobian z)) (Λ ×ˢ univ)
        (⟨(νeq : Measure X).prod (ζ : Measure Y), inferInstance⟩ : ProbabilityMeasure (X × Y))) :
    LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
      (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe)
      product.scale product.scale_positive (fun x => bound x.val) potential := by
  let fy := NativeLocalOutcome.family auxiliary
  let fp := NativeLocalOutcome.family product
  let δ := min fp.window (min fy.window (min P.window auxiliary.maps.window))
  have hδ : 0 < δ := lt_min fp.window_positive
    (lt_min fy.window_positive (lt_min P.window_positive auxiliary.maps.window_positive))
  have hwindows : δ ≤ min P.window auxiliary.maps.window :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hy : δ ≤ fy.window := (min_le_right _ _).trans (min_le_left _ _)
  have hpw : δ ≤ fp.window := min_le_left _ _
  obtain ⟨y, _⟩ := a.nonempty_core
  have hΛ : (closure V ∩ Λ).Nonempty := by
    obtain ⟨x, hx⟩ := h.nonempty_core
    exact ⟨x, subset_closure (h.basic.subset_neighborhood hx), hx⟩
  have sf : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      HasStrongFellerKernel (ActualStabilizedNoisePoint.original P auxiliary.maps L ε hε
        (hεδ.trans hwindows) V w hw.measurable product.scale product.scale_positive bound) := by
    intro ε hε hεδ
    exact P.strongFeller_live_raw_cube L ε hε ((hεδ.trans hwindows).trans (min_le_left _ _))
      (closure V) isClosed_closure.measurableSet (fun x => w x.val)
      (hw.comp continuous_subtype_val) (fun x => hw0 x.val)
      product.scale product.scale_positive (fun x => bound x.val)
      (smoothSource ε hε ((hεδ.trans hwindows).trans (min_le_left _ _)))
  have auxGap : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (ActualStabilizedNoisePoint.auxiliaryLocal P auxiliary.maps auxiliary.laws ε hε
          (hεδ.trans hwindows) 1 le_rfl) univ (fy.probability ε) := by
    intro ε hε hεδ
    obtain ⟨_, hεwindow, gap⟩ := fy.gap ε hε (hεδ.trans hy)
    let := auxiliary.laws.probability ε
    have renormalized := NormalizedGapRenormalization.restrictedNoise
      (auxiliary.laws.law ε)
      (fun z : Y × cube (ι := κ) ε => auxiliary.maps.family ε z.2.val z.1)
      (auxiliary.maps.raw_measurable ε hε hεwindow)
      univ MeasurableSet.univ (fun _ => 1) fy.weight_continuous.measurable
      auxiliary.scale 1 auxiliary.scale_positive zero_lt_one fy.weight_bound (fun _ => le_rfl)
      {x : (univ : Set Y) | x.val ∈ (univ : Set Y)} (fy.probability ε) gap
    have core_eq : {x : (univ : Set Y) | x.val ∈ (univ : Set Y)} = univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ]
    rw [core_eq] at renormalized
    exact renormalized
  have productChain (ε : ℝ≥0) (hε : 0 < ε) (hεδ : ε ≤ δ) :
      RestrictedNoise.chain (product.laws.law ε)
        (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => product.maps.family ε z.2.val z.1)
        (product.maps.raw_measurable ε hε ((hεδ.trans hpw).trans fp.window_bound))
        (closure (V ×ˢ univ)) isClosed_closure.measurableSet (fun z => w z.val.1)
        fp.weight_continuous.measurable product.scale product.scale_positive fp.weight_bound =
      ActualStabilizedNoisePoint.closedProduct P auxiliary.maps L auxiliary.laws ε hε
        (hεδ.trans hwindows) V w hw.measurable product.scale 1 product.scale_positive le_rfl bound := by
    have map_eq : (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => product.maps.family ε z.2.val z.1) =
        ActualProductRestrictedChain.joint ε (ActualProductRestrictedChain.actualMap P ε)
          (ActualProductRestrictedChain.actualMap auxiliary.maps ε) := by
      rw [ActualProductRestrictedChain.joint_eq_independentFamily]
      funext z
      exact congrFun (maps_match ε) z.2.val ▸ rfl
    simp only [ActualStabilizedNoisePoint.closedProduct, ActualStabilizedLocalPoint.closedChain,
      mul_one]
    congr 1
    exact laws_match ε
  have core_eq : {z : closure (V ×ˢ (univ : Set Y)) | z.val ∈ Λ ×ˢ univ} =
      {z | z.val.1 ∈ Λ} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
  have points (ε : ℝ≥0) (hε : 0 < ε) (hεδ : ε ≤ δ) :=
    LocalConclusions.Point.transport (productChain ε hε hεδ)
      (mul_one product.scale).symm core_eq (fp.point ε hε (hεδ.trans hpw))

  have gaps : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (ActualStabilizedNoisePoint.closedProduct P auxiliary.maps L auxiliary.laws ε hε
          (hεδ.trans hwindows) V w hw.measurable product.scale 1 product.scale_positive le_rfl bound)
        {z | z.val.1 ∈ Λ} (fp.probability ε) := by
    intro ε hε hεδ
    obtain ⟨_, _, gap⟩ := fp.gap ε hε (hεδ.trans hpw)
    rw [productChain ε hε hεδ] at gap
    have core_eq : {z : closure (V ×ˢ (univ : Set Y)) | z.val ∈ Λ ×ˢ univ} =
        {z | z.val.1 ∈ Λ} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [core_eq] at gap
    exact gap
  have heq := fp.equilibrium_unique
    (⟨(νeq : Measure X).prod (fy.equilibrium : Measure Y), inferInstance⟩ : ProbabilityMeasure (X × Y))
    (productVariational fy.equilibrium fy.equilibrium_state)
  have productLimit : (fp.initialLimit : Measure (closure (V ×ˢ (univ : Set Y)))).map Subtype.val =
      (νeq : Measure X).prod (fy.equilibrium : Measure Y) :=
    fp.map_limit.trans (congrArg (fun q : ProbabilityMeasure (X × Y) => (q : Measure (X × Y))) heq.symm)
  exact ActualStabilizedNoiseStability.stability P auxiliary.maps L auxiliary.laws
    V w hw.measurable product.scale 1 product.scale_positive le_rfl bound hw0 Λ hΛ
    δ hδ hwindows fy.probability fp.probability fp.initialLimit fp.limit
    sf auxGap points gaps y potential νeq fy.equilibrium productLimit equilibrium unique

end ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalStability
