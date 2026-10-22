module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseConstructor
public import LeanShared.Geometry.FractionalCartesianMapRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Operator.Prod

/-! The quantitative Whitney bound of a product map in the product Whitney atlas. In product charts
the coordinate of `Prod.map f g` is the pair of the factor coordinates; its iterated derivatives
are the pairs of the factor derivatives composed with the projections, whose norm is at most the
maximum of the factor norms. Hence factor bounds `δ` and `δ'` give the product bound `max δ δ'`
for the uniform distance, all derivative differences and the top Hölder seminorm. Together with
the product regularity this proves `FractionalProductCalculus`. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]

section Pair
variable {k : ℕ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The iterated derivative of `φ ∘ fst` on an open set. -/
theorem iteratedFDeriv_comp_fst {φ : E → E} {P : Set E} (hP : IsOpen P) {n : WithTop ℕ∞}
    (hφ : ContDiffOn ℝ n φ P) {y : E × F} (hy : y.1 ∈ P) (hk : (k : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ k (fun y : E × F => φ y.1) y =
      (iteratedFDeriv ℝ k φ y.1).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst ℝ E F) := by
  have open' : IsOpen (ContinuousLinearMap.fst ℝ E F ⁻¹' P) := hP.preimage continuous_fst
  have h1 := (ContinuousLinearMap.fst ℝ E F).iteratedFDerivWithin_comp_right hφ hP.uniqueDiffOn
    open'.uniqueDiffOn hy hk
  rw [iteratedFDerivWithin_of_isOpen k open' hy] at h1
  rw [show (ContinuousLinearMap.fst ℝ E F) y = y.1 from rfl,
    iteratedFDerivWithin_of_isOpen k hP hy] at h1
  exact h1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The iterated derivative of `ψ ∘ snd` on an open set. -/
theorem iteratedFDeriv_comp_snd {ψ : F → F} {Q : Set F} (hQ : IsOpen Q) {n : WithTop ℕ∞}
    (hψ : ContDiffOn ℝ n ψ Q) {y : E × F} (hy : y.2 ∈ Q) (hk : (k : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ k (fun y : E × F => ψ y.2) y =
      (iteratedFDeriv ℝ k ψ y.2).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.snd ℝ E F) := by
  have open' : IsOpen (ContinuousLinearMap.snd ℝ E F ⁻¹' Q) := hQ.preimage continuous_snd
  have h1 := (ContinuousLinearMap.snd ℝ E F).iteratedFDerivWithin_comp_right hψ hQ.uniqueDiffOn
    open'.uniqueDiffOn hy hk
  rw [iteratedFDerivWithin_of_isOpen k open' hy] at h1
  rw [show (ContinuousLinearMap.snd ℝ E F) y = y.2 from rfl,
    iteratedFDerivWithin_of_isOpen k hQ hy] at h1
  exact h1

/-- The pair of factor multilinear maps read through the projections. -/
abbrev pair (u : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E)
    (v : ContinuousMultilinearMap ℝ (fun _ : Fin k => F) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E × F) (E × F) :=
  (u.compContinuousLinearMap (fun _ => ContinuousLinearMap.fst ℝ E F)).prod
    (v.compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℝ E F))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem pair_sub (u u' : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E)
    (v v' : ContinuousMultilinearMap ℝ (fun _ : Fin k => F) F) :
    pair u v - pair u' v' = pair (u - u') (v - v') := by
  ext m <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem pair_norm_le (u : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E)
    (v : ContinuousMultilinearMap ℝ (fun _ : Fin k => F) F) :
    ‖pair u v‖ ≤ max ‖u‖ ‖v‖ := by
  rw [pair, ContinuousMultilinearMap.opNorm_prod]
  apply max_le_max
  · refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le u _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg u)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ..))
  · refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le v _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg v)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le ..))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The iterated derivative of a product of coordinate maps is the pair of factor derivatives. -/
theorem iteratedFDeriv_prodMap {φ : E → E} {ψ : F → F} {P : Set E} {Q : Set F}
    (hP : IsOpen P) (hQ : IsOpen Q) {n : WithTop ℕ∞} (hφ : ContDiffOn ℝ n φ P)
    (hψ : ContDiffOn ℝ n ψ Q) {y : E × F} (hy1 : y.1 ∈ P) (hy2 : y.2 ∈ Q)
    (hk : (k : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ k (fun y : E × F => (φ y.1, ψ y.2)) y =
      pair (iteratedFDeriv ℝ k φ y.1) (iteratedFDeriv ℝ k ψ y.2) := by
  have c1 : ContDiffAt ℝ n (fun y : E × F => φ y.1) y :=
    (hφ.contDiffAt (hP.mem_nhds hy1)).comp y contDiffAt_fst
  have c2 : ContDiffAt ℝ n (fun y : E × F => ψ y.2) y :=
    (hψ.contDiffAt (hQ.mem_nhds hy2)).comp y contDiffAt_snd
  rw [iteratedFDeriv_prodMk c1 c2 hk, iteratedFDeriv_comp_fst hP hφ hy1 hk,
    iteratedFDeriv_comp_snd hQ hψ hy2 hk]

end Pair

local instance productWhitneyCharts : ChartedSpace (E × F) (X × Y) :=
  prodChartedSpace E X F Y

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ X] in
/-- The coordinate maps of a regular map are smooth on the coordinate patches. -/
theorem WhitneyAtlas.coordinate_contDiffOn {T : X → X} (A : WhitneyAtlas (E := E) T)
    {n : ℕ} {f : X → X} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) n f) (i : Fin A.count)
    (hc : f '' closure (A.patch i) ⊆ (A.target i).source) :
    ContDiffOn ℝ n (A.coordinate f i) (A.coordinatePatch i) := by
  have hs : A.patch i ⊆ (A.source i).source := subset_closure.trans (A.patch_source i)
  have h2s : MapsTo f (A.patch i) (A.target i).source := fun x hx =>
    hc ⟨x, subset_closure hx, rfl⟩
  have he := maximalAtlas_subset_of_le (I := 𝓘(ℝ, E)) (M := X)
    (show ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top) (A.source_smooth i)
  have he' := maximalAtlas_subset_of_le (I := 𝓘(ℝ, E)) (M := X)
    (show ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top) (A.target_smooth i)
  have smooth := (contMDiffOn_iff_of_mem_maximalAtlas' he he' hs h2s).1 hf.contMDiffOn
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp] at smooth
  rw [(A.source i).image_eq_target_inter_inv_preimage hs] at smooth
  exact smooth

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ X] in
theorem WhitneyAtlas.coordinatePatch_open {T : X → X} (A : WhitneyAtlas (E := E) T)
    (i : Fin A.count) : IsOpen (A.coordinatePatch i) :=
  (A.source i).isOpen_inter_preimage_symm (A.patch_open i)

section Product
variable {T0 : X → X} {T1 : Y → Y} (A : WhitneyAtlas (E := E) T0) (B : WhitneyAtlas (E := F) T1)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem WhitneyAtlas.product_coordinate (f : X → X) (g : Y → Y) (k : Fin (A.product B).count) :
    (A.product B).coordinate (Prod.map f g) k = fun y : E × F =>
      (A.coordinate f (finProdFinEquiv.symm k).1 y.1,
        B.coordinate g (finProdFinEquiv.symm k).2 y.2) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem WhitneyAtlas.mem_product_coordinatePatch {k : Fin (A.product B).count} {y : E × F}
    (hy : y ∈ (A.product B).coordinatePatch k) :
    y.1 ∈ A.coordinatePatch (finProdFinEquiv.symm k).1 ∧
      y.2 ∈ B.coordinatePatch (finProdFinEquiv.symm k).2 :=
  ⟨⟨hy.1.1, hy.2.1⟩, ⟨hy.1.2, hy.2.2⟩⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The Whitney bound of a product map in the product atlas. -/
theorem WhitneyAtlas.product_bound {r δ δ' : ℝ} {f : X → X} {g : Y → Y}
    (hT0 : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T0)
    (hT1 : LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r T1)
    (hf : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r f)
    (hg : LeanShared.FractionalManifoldRegularity.Regular (E := F) (F := F) r g)
    (bf : A.Bound r f δ) (bg : B.Bound r g δ') :
    (A.product B).Bound r (Prod.map f g) (max δ δ') where
  uniform z := by
    rw [Prod.dist_eq]
    exact max_le_max (bf.uniform z.1) (bg.uniform z.2)
  target_control k := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ closure (A.patch _ ×ˢ B.patch _) at hz
    rw [closure_prod_eq] at hz
    exact ⟨bf.target_control _ ⟨z.1, hz.1, rfl⟩, bg.target_control _ ⟨z.2, hz.2, rfl⟩⟩
  derivatives k j hj y hy := by
    obtain ⟨hy1, hy2⟩ := A.mem_product_coordinatePatch B hy
    have hjn : (j : WithTop ℕ∞) ≤ ((⌊r⌋₊ : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
    have cf := A.coordinate_contDiffOn hf.differentiable (finProdFinEquiv.symm k).1
      (bf.target_control _)
    have cT := A.coordinate_contDiffOn hT0.differentiable (finProdFinEquiv.symm k).1
      (A.deterministic_target _)
    have cg := B.coordinate_contDiffOn hg.differentiable (finProdFinEquiv.symm k).2
      (bg.target_control _)
    have cT' := B.coordinate_contDiffOn hT1.differentiable (finProdFinEquiv.symm k).2
      (B.deterministic_target _)
    rw [A.product_coordinate B f g k, A.product_coordinate B T0 T1 k,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cf cg hy1 hy2
        hjn,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cT cT' hy1 hy2
        hjn, pair_sub]
    exact (pair_norm_le _ _).trans
      (max_le_max (bf.derivatives _ j hj _ hy1) (bg.derivatives _ j hj _ hy2))
  holder hr k y hy z hz := by
    obtain ⟨hy1, hy2⟩ := A.mem_product_coordinatePatch B hy
    obtain ⟨hz1, hz2⟩ := A.mem_product_coordinatePatch B hz
    have hjn : ((⌊r⌋₊ : ℕ) : WithTop ℕ∞) ≤ ((⌊r⌋₊ : ℕ) : WithTop ℕ∞) := le_rfl
    have cf := A.coordinate_contDiffOn hf.differentiable (finProdFinEquiv.symm k).1
      (bf.target_control _)
    have cT := A.coordinate_contDiffOn hT0.differentiable (finProdFinEquiv.symm k).1
      (A.deterministic_target _)
    have cg := B.coordinate_contDiffOn hg.differentiable (finProdFinEquiv.symm k).2
      (bg.target_control _)
    have cT' := B.coordinate_contDiffOn hT1.differentiable (finProdFinEquiv.symm k).2
      (B.deterministic_target _)
    rw [A.product_coordinate B f g k, A.product_coordinate B T0 T1 k,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cf cg hy1 hy2
        hjn,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cT cT' hy1 hy2
        hjn,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cf cg hz1 hz2
        hjn,
      iteratedFDeriv_prodMap (A.coordinatePatch_open _) (B.coordinatePatch_open _) cT cT' hz1 hz2
        hjn, pair_sub, pair_sub, pair_sub]
    have θ : 0 ≤ r - (⌊r⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hf.nonnegative)
    have d1 : ‖y.1 - z.1‖ ^ (r - (⌊r⌋₊ : ℝ)) ≤ ‖y - z‖ ^ (r - (⌊r⌋₊ : ℝ)) :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_fst_le (y - z)) θ
    have d2 : ‖y.2 - z.2‖ ^ (r - (⌊r⌋₊ : ℝ)) ≤ ‖y - z‖ ^ (r - (⌊r⌋₊ : ℝ)) :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_snd_le (y - z)) θ
    refine (pair_norm_le _ _).trans (max_le ?_ ?_)
    · exact (bf.holder hr _ _ hy1 _ hz1).trans (mul_le_mul (le_max_left _ _) d1
        (Real.rpow_nonneg (norm_nonneg _) _)
        (le_trans (le_trans (norm_nonneg _) (bf.derivatives _ 0 (Nat.zero_le _) _ hy1))
          (le_max_left _ _)))
    · exact (bg.holder hr _ _ hy2 _ hz2).trans (mul_le_mul (le_max_right _ _) d2
        (Real.rpow_nonneg (norm_nonneg _) _)
        (le_trans (le_trans (norm_nonneg _) (bg.derivatives _ 0 (Nat.zero_le _) _ hy2))
          (le_max_right _ _)))

end Product

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The product calculus record, with no remaining source. -/
theorem proved_fractionalProductCalculus (r : ℝ) :
    FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) r where
  regular _ _ hf hg := hf.prod_map hg
  whitney _ _ _ _ A B hT0 hT1 hf hg _ _ bf bg := A.product_bound B hT0 hT1 hf hg bf bg

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
