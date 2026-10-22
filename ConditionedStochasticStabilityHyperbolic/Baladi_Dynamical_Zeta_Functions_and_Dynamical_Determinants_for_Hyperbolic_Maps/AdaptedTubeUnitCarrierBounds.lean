module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelUniformBounds
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageLetters
public import LeanShared.Analysis.ActualWordPrefixOrbit

meta import Lean.LibrarySuggestions.Basic
/-! Global bounds of the adapted tube carrier from chart-pair rows in the
form produced by the polarized chart-pair bound. Rows for every single
letter give a uniform bound on every constructed generator (the one-step
bound); rows for a literal chronological word give the completed two-norm
word bound. -/
-- The theorem statements below contain the whole carrier; exclude them from
-- the library-suggestion symbol-frequency export, which does not share subterms.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierBounds"

@[expose] public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierBounds
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open FiniteRegularTransferRealization
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base}
  (atlas : ChartAtlas system) {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : tubes => atlas.normalizedTube radius i.val))
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (positiveStable : 0 < system.framing.stableDimension)
  (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate)))
  (exponent : Bool → ℝ) (margin : ∀ a, exponent a ≤ b)
  {lossW : ℝ} (hW : 0 < lossW)

/-- Chart-pair rows, in the form produced by the polarized chart-pair bound,
for one map, one weight, one strong coefficient and one weak remainder. -/
def Rows (Fw : M → M) (gw : M → ℝ) (strong : ℝ) (remainder : tubes → tubes → ℝ) : Prop :=
  letI := charts atlas; ∀ i j : tubes, ∀ u : SchwartzJetSpace.supportedCore
      (ChartLocalization.localSupport (atlas.normalizedTubeChart j.val) (fun m => (d.beta j m : ℂ))),
    ∃ output : EuclideanSmoothHolderCore.space
        (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
          (localization atlas d) i).closure hb hb1,
      (∀ z, EuclideanSmoothHolderCore.physical
        (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
          (localization atlas d) i).closure hb hb1 output z =
        ChartPairTransfer.pair (atlas.normalizedTubeChart i.val) (atlas.normalizedTubeChart j.val)
          (fun m => (d.beta i m : ℂ)) Fw gw u.val z) ∧
      ‖CompactHolderPhysicalBlocks.realize (volume : Measure (Leaf system))
        (unitSlope system positiveStable) (unitLeaves system positiveStable) radial angle
        (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
          (localization atlas d) i) hb hb1 exponent margin output‖ ≤
      strong * ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
          (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
          (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
            (localization atlas d) j) hb hb1 exponent margin () u‖ +
      remainder i j * ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
          (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
          (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
            (localization atlas d) j) hb hb1 (fun a => exponent a - lossW)
          (fun a => (sub_le_self _ hW.le).trans (margin a)) () u‖

omit [FiniteDimensional ℝ E] in
/-- Rows persist under a larger strong coefficient. -/
theorem Rows.mono {Fw : M → M} {gw : M → ℝ} {strong strong' : ℝ} {remainder : tubes → tubes → ℝ}
    (rows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw gw strong remainder)
    (larger : strong ≤ strong') :
    Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw gw strong' remainder := by
  intro i j u
  have row := rows i j u
  exact ⟨row.choose, row.choose_spec.1, row.choose_spec.2.trans
    (add_le_add (mul_le_mul_of_nonneg_right larger (norm_nonneg _)) le_rfl)⟩

omit [FiniteDimensional ℝ E] in
/-- Rows transport along equalities of map and weight. -/
theorem Rows.congr {Fw Fw' : M → M} {gw gw' : M → ℝ} {strong : ℝ} {remainder : tubes → tubes → ℝ}
    (rows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw gw strong remainder)
    (sameF : Fw = Fw') (sameG : gw = gw') :
    Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw' gw' strong remainder := by
  subst sameF sameG
  exact rows

variable (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
  {V : Set M} (openV : IsOpen V) (region : V ⊆ d.capture)
  {r : ℝ} (F : Paper.RegularNoise.Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
  (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (hT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g : M → ℝ} {q : ℝ} (hbq : b < q)
  (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
  (support : tsupport g ⊆ V)
  (lossH : ℝ) (hH : 0 < lossH)
  (η : NNReal) (cap : η ≤ (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).window)

local notation "carrier" => AdaptedTubeUnitCarrier.model atlas d μE openV region hb hb1 F hr regularT
  hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap

omit [FiniteDimensional ℝ E] in
/-- Rows give the chart-pair membership required by the local pair transfer. -/
theorem pairMember_of_rows (Fw : M → M) (gw : M → ℝ) (strong : ℝ) (remainder : tubes → tubes → ℝ)
    (rows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw gw strong remainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support (carrier).atlas (carrier).localization j)),
      ChartPairTransfer.pair ((carrier).atlas i) ((carrier).atlas j)
        ((carrier).localization.cutoff i) Fw gw f.val ∈ ((carrier).localView i).range := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro i j f
  obtain ⟨output, physical, _⟩ := rows i.val j.val f
  exact ⟨output, funext fun z => (localView_apply atlas d μE openV region hb hb1 F hr regularT hT
    hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap i output z).trans
    (physical z)⟩

omit [FiniteDimensional ℝ E] in
/-- Rows give the carrier's chart-pair estimate. -/
theorem estimate_of_rows (Fw : M → M) (gw : M → ℝ) (strong : ℝ) (remainder : tubes → tubes → ℝ)
    (rows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW Fw gw strong remainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalModelUniformBounds.PairEstimate (carrier) Fw gw strong
      (fun i j => remainder i.val j.val) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact ⟨pairMember_of_rows atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV
      region F hr regularT hT hbq hg support lossH hH η cap Fw gw strong remainder rows,
    pairBound_of_rows atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable
      radial angle exponent margin lossH lossW hH hW η cap Fw gw
      (pairMember_of_rows atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV
        region F hr regularT hT hbq hg support lossH hH η cap Fw gw strong remainder rows)
      strong remainder rows⟩

/-- The actual noisy letter at scale `ε` with control `c`, as a carrier parameter. -/
abbrev letter (ε : NNReal) (hp : 0 < ε) (hl : ε ≤ η) (c : Paper.RegularNoise.cube (ι := ι) ε) :=
  letI := charts atlas;
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
  Paper.RegularNoise.MapImage.noise (maps atlas F regularT) hr η
    (cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below)
    ε hp hl c

omit [FiniteDimensional ℝ E] in
/-- D4 input: rows for every positive-scale noise map give an estimate, with
one strong cap and one remainder, for every carrier parameter. -/
theorem letter_estimates (positiveη : 0 < η) (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : tubes → tubes → ℝ)
    (rows : ∀ (ε : NNReal), 0 < ε → ε ≤ η → ∀ c : Paper.RegularNoise.cube (ι := ι) ε,
      Rows atlas d hb hb1 positiveStable radial angle exponent margin hW (F.family ε c.val) g
        Smax remainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ a, ∃ strong, 0 ≤ strong ∧ strong ≤ Smax ∧
      PhysicalModelUniformBounds.PairEstimate (carrier) ((carrier).maps a) (carrier).weight strong
        (fun i j => remainder i.val j.val) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro a
  have fam := Paper.RegularNoise.MapImage.exists_family (maps atlas F regularT) hr η
    (cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below)
    positiveη a
  have row := rows fam.choose fam.choose_spec.1 fam.choose_spec.2.1 fam.choose_spec.2.2.choose
  refine ⟨Smax, hS, le_rfl, estimate_of_rows atlas d hb hb1 positiveStable radial angle exponent
    margin hW μE openV region F hr regularT hT hbq hg support lossH hH η cap
    ((carrier).maps a) (carrier).weight Smax remainder ?_⟩
  exact Rows.congr atlas d hb hb1 positiveStable radial angle exponent margin hW row
    (funext fun x => (congrFun fam.choose_spec.2.2.choose_spec x).symm) rfl

omit [FiniteDimensional ℝ E] in
/-- D4: uniform bound on every constructed generator. -/
theorem generator_bound_of_rows (positiveη : 0 < η) (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : tubes → tubes → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (rows : ∀ (ε : NNReal), 0 < ε → ε ≤ η → ∀ c : Paper.RegularNoise.cube (ι := ι) ε,
      Rows atlas d hb hb1 positiveStable radial angle exponent margin hW (F.family ε c.val) g
        Smax remainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelUniformBounds.GeneratorBound (carrier) L := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact ⟨PhysicalModelUniformBounds.oneStepConstant (carrier) Smax (fun i j => remainder i.val j.val),
    PhysicalModelUniformBounds.oneStepConstant_nonneg (carrier) Smax hS _ (fun i j => hR _ _),
    fun a => PhysicalModelUniformBounds.generator_bound (carrier) Smax hS _ (fun i j => hR _ _)
      (letter_estimates atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV region
        F hr regularT hT hbq hg support lossH hH η cap positiveη Smax hS remainder rows) a⟩

omit [FiniteDimensional ℝ E] in
/-- D5: rows for a literal noise word give the completed two-norm bound for
the corresponding word of constructed generators. -/
theorem word_bound_of_rows (positiveη : 0 < η) (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : tubes → tubes → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (rows : ∀ (ε : NNReal), 0 < ε → ε ≤ η → ∀ c : Paper.RegularNoise.cube (ι := ι) ε,
      Rows atlas d hb hb1 positiveStable radial angle exponent margin hW (F.family ε c.val) g
        Smax remainder)
    {K : ℕ} (ε : NNReal) (hp : 0 < ε) (hl : ε ≤ η)
    (control : Fin K → Paper.RegularNoise.cube (ι := ι) ε)
    (strong : ℝ) (hstrong : 0 ≤ strong) (wordRemainder : tubes → tubes → ℝ)
    (hW' : ∀ i j, 0 ≤ wordRemainder i j)
    (wordRows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW
      (CylinderPrincipalCoefficient.prefixOrbit
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) control K)
      (fun m => ∏ k ∈ Finset.range K, g (CylinderPrincipalCoefficient.prefixOrbit
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) control k m))
      strong wordRemainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalModelUniformBounds.WordBound (carrier)
      (List.ofFn fun k => letter atlas d hb hb1 μE openV region F hr regularT hT hbq hg support
        η cap ε hp hl (control k))
      ((Fintype.card (carrier).localization.indices : ℝ) ^ 2 * strong)
      (∑ i, ∑ j, (fun i j : (carrier).localization.indices => wordRemainder i.val j.val) i j) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  have est := estimate_of_rows atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV
    region F hr regularT hT hbq hg support lossH hH η cap
    (ActualFiniteRegularWord.orbit (carrier).maps
      (List.ofFn fun k => letter atlas d hb hb1 μE openV region F hr regularT hT hbq hg support
        η cap ε hp hl (control k)))
    (ActualWordMicrolocalBound.realWeight (carrier).maps (carrier).weight
      (List.ofFn fun k => letter atlas d hb hb1 μE openV region F hr regularT hT hbq hg support
        η cap ε hp hl (control k)))
    strong wordRemainder
    (Rows.congr atlas d hb hb1 positiveStable radial angle exponent margin hW wordRows
      (funext fun y => (ActualWordPrefixOrbit.orbit_ofFn (carrier).maps
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) _ control
        (fun _ => rfl) y).symm)
      (funext fun y => (ActualWordPrefixOrbit.realWeight_ofFn (carrier).maps
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) (carrier).weight _ control
        (fun _ => rfl) y).symm))
  exact PhysicalModelUniformBounds.wordBound_of_estimates (carrier) Smax
    (fun i j => remainder i.val j.val) (fun i j => hR _ _)
    (letter_estimates atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV region
      F hr regularT hT hbq hg support lossH hH η cap positiveη Smax hS remainder rows)
    (List.ofFn fun k => letter atlas d hb hb1 μE openV region F hr regularT hT hbq hg support
      η cap ε hp hl (control k))
    strong hstrong (fun i j => wordRemainder i.val j.val) (fun i j => hW' _ _) est

omit [FiniteDimensional ℝ E] in
theorem card_indices :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    Fintype.card (carrier).localization.indices = Fintype.card tubes := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact Fintype.card_congr (FiniteLocalizationReindex.indexEquiv (fun j => atlas.normalizedTubeChart j)
    (localization atlas d))

omit [FiniteDimensional ℝ E] in
theorem sum_indices (R : tubes → tubes → ℝ) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    (∑ i : (carrier).localization.indices, ∑ j : (carrier).localization.indices, R i.val j.val) =
      ∑ i : tubes, ∑ j : tubes, R i j := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact Fintype.sum_equiv (FiniteLocalizationReindex.indexEquiv (fun j => atlas.normalizedTubeChart j)
    (localization atlas d)) _ _ (fun i => Fintype.sum_equiv (FiniteLocalizationReindex.indexEquiv
      (fun j => atlas.normalizedTubeChart j) (localization atlas d)) _ _ (fun j => rfl))

omit [FiniteDimensional ℝ E] in
/-- D5 with constants indexed by the tubes themselves. -/
theorem word_bound_of_rows' (positiveη : 0 < η) (Smax : ℝ) (hS : 0 ≤ Smax)
    (remainder : tubes → tubes → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (rows : ∀ (ε : NNReal), 0 < ε → ε ≤ η → ∀ c : Paper.RegularNoise.cube (ι := ι) ε,
      Rows atlas d hb hb1 positiveStable radial angle exponent margin hW (F.family ε c.val) g
        Smax remainder)
    {K : ℕ} (ε : NNReal) (hp : 0 < ε) (hl : ε ≤ η)
    (control : Fin K → Paper.RegularNoise.cube (ι := ι) ε)
    (strong : ℝ) (hstrong : 0 ≤ strong) (wordRemainder : tubes → tubes → ℝ)
    (hW' : ∀ i j, 0 ≤ wordRemainder i j)
    (wordRows : Rows atlas d hb hb1 positiveStable radial angle exponent margin hW
      (CylinderPrincipalCoefficient.prefixOrbit
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) control K)
      (fun m => ∏ k ∈ Finset.range K, g (CylinderPrincipalCoefficient.prefixOrbit
        (fun c : Paper.RegularNoise.cube (ι := ι) ε => F.family ε c.val) control k m))
      strong wordRemainder) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalModelUniformBounds.WordBound (carrier)
      (List.ofFn fun k => letter atlas d hb hb1 μE openV region F hr regularT hT hbq hg support
        η cap ε hp hl (control k))
      ((Fintype.card tubes : ℝ) ^ 2 * strong) (∑ i : tubes, ∑ j : tubes, wordRemainder i j) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  have word := word_bound_of_rows atlas d hb hb1 positiveStable radial angle exponent margin hW μE
    openV region F hr regularT hT hbq hg support lossH hH η cap positiveη Smax hS remainder hR rows
    ε hp hl control strong hstrong wordRemainder hW' wordRows
  exact PhysicalModelUniformBounds.WordBound.mono (carrier) word
    (le_of_eq (congrArg (fun n : ℕ => (n : ℝ) ^ 2 * strong)
      (card_indices atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV region
        F hr regularT hT hbq hg support lossH hH η cap)))
    (le_of_eq (sum_indices atlas d hb hb1 positiveStable radial angle exponent margin hW μE openV
      region F hr regularT hT hbq hg support lossH hH η cap wordRemainder))

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierBounds
