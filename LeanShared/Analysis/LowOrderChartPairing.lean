module
public import LeanShared.Analysis.LowOrderBlockPairing
public import LeanShared.Analysis.ConeFourierUniformResolution

/-!
Low-order chart pairing: if every
dyadic cone block of a Schwartz function `f` has integrals at most
`2^{-t(s) n} B` over the parallel affine leaves `{u + L u + w}`, then for every
compactly supported Hölder test `φ` of order `b` with `b + t(s) > 0`,
`|∫ f φ| ≤ C ‖φ‖_{C^b} B`. The low block uses the compact support of the test,
each high block gains `2^{-bn}` by cancellation, and the dyadic partial sums
reconstruct the pairing.
-/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory Filter
open scoped SchwartzMap BoundedContinuousFunction Topology
namespace LeanShared.LowOrderChartPairing
open FourierSchwartzKernel ConeFourierBlocks ConeDyadicSymbols ConeFourierPairingResolution
open LowOrderBlockPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus : Set E}

/-- The fixed high-frequency symbol of one sign. -/
def highSymbol (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (s : Bool) : 𝓢(E, ℂ) :=
  FourierSchwartzKernel.symbol (high χ Φ.toFun s) (high_hasCompactSupport χ Φ.toFun s)
    (high_smooth χ Φ s)

theorem highSymbol_annulus (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (s : Bool)
    (ξ : E) (nonzero : highSymbol χ Φ s ξ ≠ 0) : 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 := by
  by_contra h
  apply nonzero
  change (highReal χ Φ.toFun s ξ : ℂ) = 0
  rw [Complex.ofReal_eq_zero]
  unfold highReal
  rcases not_and_or.mp h with h | h
  · rw [annular_zero_near_origin χ (le_of_lt (not_le.mp h)), mul_zero]
  · rw [annular_zero_outside χ (le_of_lt (not_le.mp h)), mul_zero]

theorem symbols_high (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) {n : ℕ} (hn : n ≠ 0)
    (s : Bool) :
    symbols χ Φ (n, s) = dilateSymbol (highSymbol χ Φ s) ((2 : ℝ) ^ n) (pow_pos (by norm_num) _) := by
  unfold symbols DyadicSymbols.symbolsFromMultipliers DyadicSymbols.symbol
  simp only [hn, ↓reduceIte]
  rfl

theorem partialSum_pairing (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (N : ℕ)
    (f : 𝓢(E, ℂ)) (φ : E → ℂ) (integrable : Integrable φ) :
    (∫ x, partialSum χ Φ N f x * φ x) =
      ∑ n ∈ Finset.range (N + 1), ∑ s : Bool, ∫ x, block (symbols χ Φ (n, s)) f x * φ x := by
  have hint : ∀ j : ℕ × Bool, Integrable (fun x => block (symbols χ Φ j) f x * φ x) := fun j =>
    integrable.bdd_mul (block (symbols χ Φ j) f).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℂ _ x)
  simp only [partialSum, sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun s _ => hint (n, s)))]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_finsetSum _ (fun s _ => hint (n, s))]

/-- The low block: no cancellation; the compact support of the test gives the leaf weight. -/
theorem low_bound (P : Submodule ℝ E) (L : P →L[ℝ] Pᗮ) {K : Set E} (compact : IsCompact K)
    {b : ℝ} {m : ℕ} (hm : (Module.finrank ℝ Pᗮ : ℝ) < m) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : 𝓢(E, ℂ)) (v : BoundedHolderSpace.graph E b),
      tsupport (BoundedHolderSpace.physical E b v) ⊆ K → ∀ A : ℝ,
      (∀ w : Pᗮ, ∫ u : P, ‖g ((u : E) + (L u : E) + (w : E))‖ ≤ A) →
      ‖∫ x, g x * BoundedHolderSpace.physical E b v x‖ ≤ D * ‖v‖ * A := by
  obtain ⟨R, hR, radius⟩ := compact.isBounded.exists_pos_norm_le
  let c : ℝ := (1 + (1 + ‖L‖) * R) ^ m
  have hc : 0 ≤ c := pow_nonneg (by nlinarith [norm_nonneg L]) m
  let I : ℝ := ∫ w : Pᗮ, GraphLeafNorm.radialWeight (m : ℝ) w
  have hI : 0 ≤ I := integral_nonneg fun w => GraphLeafNorm.radialWeight_nonneg _ w
  refine ⟨c * I, mul_nonneg hc hI, ?_⟩
  intro g v support A leaves
  let φ := BoundedHolderSpace.physical E b v
  have hφ : ∀ x, ‖φ x‖ ≤ ‖v‖ := fun x =>
    (φ.norm_coe_le_norm x).trans (BoundedHolderSpace.physical_norm_le E b v)
  have product : Integrable (fun x => g x * φ x) :=
    g.integrable.mul_bdd φ.continuous.aestronglyMeasurable (ae_of_all _ hφ)
  have test : ∀ (u : P) (w : Pᗮ), ‖φ ((u : E) + (L u : E) + (w : E))‖ ≤
      (‖v‖ * c) * GraphLeafNorm.radialWeight (m : ℝ) w := by
    intro u w
    by_cases zero : φ ((u : E) + (L u : E) + (w : E)) = 0
    · rw [zero, norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hc) (GraphLeafNorm.radialWeight_nonneg _ _)
    · have inK : (u : E) + (L u : E) + (w : E) ∈ K :=
        support (subset_tsupport _ (Function.mem_support.mpr zero))
      have hx := radius _ inK
      have hw : ‖(w : E)‖ ≤ (1 + ‖L‖) * R :=
        (oblique_norm P L u w).trans (mul_le_mul_of_nonneg_left hx (by linarith [norm_nonneg L]))
      have weight : 1 ≤ c * GraphLeafNorm.radialWeight (m : ℝ) w := by
        unfold GraphLeafNorm.radialWeight
        have h0 : 0 < 1 + ‖w‖ := by linarith [norm_nonneg w]
        rw [Real.rpow_neg h0.le, Real.rpow_natCast, ← div_eq_mul_inv,
          one_le_div (pow_pos h0 m)]
        exact pow_le_pow_left₀ h0.le (by
          have : ‖w‖ = ‖(w : E)‖ := rfl
          linarith) m
      calc ‖φ ((u : E) + (L u : E) + (w : E))‖ ≤ ‖v‖ := hφ _
        _ = ‖v‖ * 1 := (mul_one _).symm
        _ ≤ ‖v‖ * (c * GraphLeafNorm.radialWeight (m : ℝ) w) :=
            mul_le_mul_of_nonneg_left weight (norm_nonneg _)
        _ = (‖v‖ * c) * GraphLeafNorm.radialWeight (m : ℝ) w := by ring
  have pairing := ObliqueLeafPairing.bound P L g φ A (‖v‖ * c) (mul_nonneg (norm_nonneg _) hc)
    (fun w : Pᗮ => GraphLeafNorm.radialWeight (m : ℝ) w)
    (fun w => GraphLeafNorm.radialWeight_nonneg _ _)
    (GraphLeafNorm.integrable_radialWeight (volume : Measure Pᗮ) hm) product
    (fun w => oblique_integrable P L g w) leaves test
  calc ‖∫ x, g x * φ x‖ ≤ (‖v‖ * c * A) * I := pairing
    _ = c * I * ‖v‖ * A := by ring

theorem dyadic_factor (b t : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ n) ^ b)⁻¹ * ((2 : ℝ) ^ (t * n))⁻¹ = ((2 : ℝ) ^ (-(b + t))) ^ n := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(b + t))) n, ← Real.rpow_mul h2.le,
    ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul h2.le, ← mul_inv,
    ← Real.rpow_add h2, ← Real.rpow_neg h2.le]
  congr 1
  ring

theorem geometric_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), q ^ n ≤ (1 - q)⁻¹ := by
  rw [geom_sum_eq (ne_of_lt hq1)]
  rw [div_eq_mul_inv, show q ^ (N + 1) - 1 = -(1 - q ^ (N + 1)) by ring,
    show q - 1 = -(1 - q) by ring, neg_mul, inv_neg, mul_neg, neg_neg]
  have h1 : 0 < 1 - q := by linarith
  have hp : 0 ≤ q ^ (N + 1) := pow_nonneg hq0 _
  calc (1 - q ^ (N + 1)) * (1 - q)⁻¹ ≤ 1 * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr h1.le)
    _ = (1 - q)⁻¹ := one_mul _

theorem shifted_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, q ^ (n + 1) ≤ (1 - q)⁻¹ := by
  have h := geometric_bound hq0 hq1 N
  rw [Finset.sum_range_succ', pow_zero] at h
  linarith

theorem series_bound {D0 : ℝ} (D q : Bool → ℝ) (hD : ∀ s, 0 ≤ D s)
    (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∀ s, q s < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ∑ s : Bool, (if n = 0 then D0 else D s * q s ^ n) ≤
      2 * D0 + ∑ s : Bool, D s * (1 - q s)⁻¹ := by
  simp only [Fintype.sum_bool]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have ht := mul_le_mul_of_nonneg_left (shifted_geometric (hq0 true) (hq1 true) N) (hD true)
  have hf := mul_le_mul_of_nonneg_left (shifted_geometric (hq0 false) (hq1 false) N) (hD false)
  linarith

/-- The single-chart low-order pairing bound. -/
theorem chart_bound (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (P : Submodule ℝ E)
    (L : P →L[ℝ] Pᗮ) {K : Set E} (compact : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (t : Bool → ℝ) (ht : ∀ s, 0 < b + t s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(E, ℂ)) (v : BoundedHolderSpace.graph E b),
      tsupport (BoundedHolderSpace.physical E b v) ⊆ K → ∀ B : ℝ, 0 ≤ B →
      (∀ (n : ℕ) (s : Bool) (w : Pᗮ), ∫ u : P, ‖block (symbols χ Φ (n, s)) f
          ((u : E) + (L u : E) + (w : E))‖ ≤ ((2 : ℝ) ^ (t s * n))⁻¹ * B) →
      ‖∫ x, f x * BoundedHolderSpace.physical E b v x‖ ≤ C * ‖v‖ * B := by
  let m : ℕ := Module.finrank ℝ Pᗮ + 1
  have hm : (Module.finrank ℝ Pᗮ : ℝ) < m := by
    simp only [m, Nat.cast_add, Nat.cast_one]; linarith
  obtain ⟨D0, hD0, low⟩ := low_bound P L compact (b := b) hm
  have highs := fun s : Bool => block_bound_oblique (highSymbol χ Φ s)
    (highSymbol_annulus χ Φ s) χ P L compact hb hb1 hm
  choose D hD high using highs
  let q : Bool → ℝ := fun s => (2 : ℝ) ^ (-(b + t s))
  have hq0 : ∀ s, 0 ≤ q s := fun s => Real.rpow_nonneg (by norm_num) _
  have hq1 : ∀ s, q s < 1 := fun s =>
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [ht s])
  let C : ℝ := 2 * D0 + ∑ s : Bool, D s * (1 - q s)⁻¹
  have hC : 0 ≤ C := by
    have : ∀ s ∈ (Finset.univ : Finset Bool), 0 ≤ D s * (1 - q s)⁻¹ := fun s _ =>
      mul_nonneg (hD s) (inv_nonneg.mpr (by linarith [hq1 s]))
    have := Finset.sum_nonneg this
    positivity
  refine ⟨C, hC, ?_⟩
  intro f v support B hB leaves
  let φ := BoundedHolderSpace.physical E b v
  have hφint : Integrable (φ : E → ℂ) := by
    have hcs : HasCompactSupport (φ : E → ℂ) :=
      IsCompact.of_isClosed_subset compact (isClosed_tsupport _) support
    exact φ.continuous.integrable_of_hasCompactSupport hcs
  -- each term
  have term : ∀ (n : ℕ) (s : Bool),
      ‖∫ x, block (symbols χ Φ (n, s)) f x * φ x‖ ≤
        (if n = 0 then D0 else D s * q s ^ n) * ‖v‖ * B := by
    intro n s
    by_cases hn : n = 0
    · subst hn
      have h := low (block (symbols χ Φ (0, s)) f) v support B (fun w => by
        have := leaves 0 s w
        simpa only [Nat.cast_zero, mul_zero, Real.rpow_zero, inv_one, one_mul] using this)
      simpa only [↓reduceIte] using h
    · have hr : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      rw [symbols_high χ Φ hn s]
      have h := high s f v support ((2 : ℝ) ^ n) hr (((2 : ℝ) ^ (t s * n))⁻¹ * B) (fun w => by
        have := leaves n s w
        rwa [symbols_high χ Φ hn s] at this)
      simp only [hn, ↓reduceIte]
      calc _ ≤ D s * ‖v‖ * (((2 : ℝ) ^ n) ^ b)⁻¹ * (((2 : ℝ) ^ (t s * n))⁻¹ * B) := h
        _ = D s * ((((2 : ℝ) ^ n) ^ b)⁻¹ * ((2 : ℝ) ^ (t s * n))⁻¹) * ‖v‖ * B := by ring
        _ = D s * q s ^ n * ‖v‖ * B := by rw [dyadic_factor]
  -- partial sums are uniformly bounded
  have partialBound : ∀ N : ℕ, ‖∫ x, partialSum χ Φ N f x * φ x‖ ≤ C * ‖v‖ * B := by
    intro N
    rw [partialSum_pairing χ Φ N f φ hφint]
    have hvB : 0 ≤ ‖v‖ * B := mul_nonneg (norm_nonneg _) hB
    calc ‖∑ n ∈ Finset.range (N + 1), ∑ s : Bool, ∫ x, block (symbols χ Φ (n, s)) f x * φ x‖
        ≤ ∑ n ∈ Finset.range (N + 1), ∑ s : Bool,
            ‖∫ x, block (symbols χ Φ (n, s)) f x * φ x‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
      _ ≤ ∑ n ∈ Finset.range (N + 1), ∑ s : Bool,
            (if n = 0 then D0 else D s * q s ^ n) * (‖v‖ * B) := by
          apply Finset.sum_le_sum; intro n _; apply Finset.sum_le_sum; intro s _
          exact (term n s).trans_eq (by ring)
      _ = (∑ n ∈ Finset.range (N + 1), ∑ s : Bool, (if n = 0 then D0 else D s * q s ^ n)) *
            (‖v‖ * B) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun n _ => (Finset.sum_mul _ _ _).symm
      _ ≤ C * (‖v‖ * B) :=
          mul_le_mul_of_nonneg_right (series_bound (D0 := D0) D q hD hq0 hq1 N) hvB
      _ = C * ‖v‖ * B := by ring
  exact le_of_tendsto ((ConeFourierUniformResolution.pairing_converges χ Φ f φ hφint).norm)
    (Eventually.of_forall partialBound)

end LeanShared.LowOrderChartPairing
