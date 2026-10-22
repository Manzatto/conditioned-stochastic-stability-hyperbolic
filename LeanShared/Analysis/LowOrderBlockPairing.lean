module
public import LeanShared.Analysis.AnnularDualCutoff
public import LeanShared.Analysis.FourierHolderRadialEnvelope
public import LeanShared.Analysis.OrthogonalLeafPairing
public import LeanShared.Analysis.ObliqueLeafPairing
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.AffineGraphSchwartzIntegrability

/-!
Low-order pairing of one dyadic Fourier block with a compactly supported
Hölder test. The radial dual cutoff
absorbs the block (`block τ (block σ f) = block σ f` when `τ = 1` on the
support of `σ`), the dual kernel is moved onto the test by Fubini (it is even),
the transposed test decays like `r^{-b} (1+|x|)^{-m}` by Hölder cancellation,
and the orthogonal leaf pairing bounds the pairing by the supremum of the
block's integrals over the parallel affine leaves `P + w`.
-/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction FourierTransform
namespace LeanShared.LowOrderBlockPairing
open FourierSchwartzKernel ConeFourierBlocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A block whose symbol is one on the support of another absorbs it. -/
theorem block_absorb (σ τ : 𝓢(E, ℂ)) (cutoff : ∀ ξ, σ ξ ≠ 0 → τ ξ = 1) (f : 𝓢(E, ℂ)) :
    block τ (block σ f) = block σ f := by
  have h : 𝓕 (block τ (block σ f)) = 𝓕 (block σ f) := by
    ext ξ
    rw [fourier_block, fourier_block]
    by_cases zero : σ ((2 * Real.pi) • ξ) = 0
    · rw [zero, zero_mul, mul_zero]
    · rw [cutoff _ zero, one_mul]
  have := congrArg (fun g : 𝓢(E, ℂ) => 𝓕⁻ g) h
  simpa only [FourierPair.fourierInv_fourier_eq] using this

/-- The kernel of an even symbol is even. -/
theorem kernel_neg (σ : 𝓢(E, ℂ)) (even : ∀ ξ, σ (-ξ) = σ ξ) (x : E) :
    kernel σ (-x) = kernel σ x := by
  rw [kernel_apply, kernel_apply]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    simp only [inner_neg_left, inner_neg_right, neg_neg, even]

/-- Fubini: the block of a Schwartz function paired with a bounded test equals the function
paired with the convolution of the test by the (even) kernel. -/
theorem pairing_transpose (τ : 𝓢(E, ℂ)) (even : ∀ ξ, τ (-ξ) = τ ξ) (g : 𝓢(E, ℂ))
    (φ : E →ᵇ ℂ) :
    (∫ x, block τ g x * φ x) = ∫ y, g y * ∫ z, kernel τ z * φ (y - z) := by
  have hK : Integrable (kernel τ) := kernel_integrable τ
  have hg : Integrable (g : E → ℂ) := g.integrable
  have joint : Integrable (fun p : E × E => kernel τ (p.1 - p.2) * g p.2 * φ p.1)
      (volume.prod volume) := by
    have base : Integrable (fun p : E × E => g p.2 * kernel τ (p.1 - p.2))
        (volume.prod volume) :=
      hg.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ) hK
    refine (base.bdd_mul (c := ‖φ‖) (φ.continuous.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun p => φ.norm_coe_le_norm p.1)).congr (ae_of_all _ fun p => ?_)
    change φ p.1 * (g p.2 * kernel τ (p.1 - p.2)) = kernel τ (p.1 - p.2) * g p.2 * φ p.1
    ring
  calc (∫ x, block τ g x * φ x)
      = ∫ x, ∫ y, kernel τ (x - y) * g y * φ x := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [block_apply, ← integral_mul_const]
    _ = ∫ y, ∫ x, kernel τ (x - y) * g y * φ x := integral_integral_swap joint
    _ = ∫ y, g y * ∫ z, kernel τ z * φ (y - z) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          dsimp only
          have shift : (∫ x, kernel τ (x - y) * g y * φ x) =
              ∫ z, kernel τ z * g y * φ (z + y) := by
            rw [← integral_add_right_eq_self (fun x => kernel τ (x - y) * g y * φ x) y]
            simp only [add_sub_cancel_right]
          have flip : (∫ z, kernel τ z * g y * φ (z + y)) =
              ∫ z, kernel τ z * g y * φ (y - z) := by
            rw [← integral_neg_eq_self]
            apply integral_congr_ae
            exact ae_of_all _ fun z => by
              dsimp only
              rw [kernel_neg τ even, neg_add_eq_sub]
          rw [shift, flip, ← integral_const_mul]
          apply integral_congr_ae
          exact ae_of_all _ fun z => by ring

theorem dual_even (χ : ConeDyadicSymbols.RadialCutoff) (r : ℝ) (hr : 0 < r) (ξ : E) :
    dilateSymbol (AnnularDualCutoff.symbol (E := E) χ) r hr (-ξ) =
      dilateSymbol (AnnularDualCutoff.symbol (E := E) χ) r hr ξ := by
  rw [dilateSymbol_apply, dilateSymbol_apply, smul_neg, AnnularDualCutoff.apply,
    AnnularDualCutoff.apply, norm_neg]

theorem dual_absorbs (σ : 𝓢(E, ℂ)) (annulus : ∀ ξ, σ ξ ≠ 0 → 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (χ : ConeDyadicSymbols.RadialCutoff) (r : ℝ) (hr : 0 < r) (ξ : E)
    (nonzero : dilateSymbol σ r hr ξ ≠ 0) :
    dilateSymbol (AnnularDualCutoff.symbol (E := E) χ) r hr ξ = 1 := by
  rw [dilateSymbol_apply] at nonzero ⊢
  obtain ⟨lower, upper⟩ := annulus _ nonzero
  exact AnnularDualCutoff.one χ lower upper

theorem norm_le_add (P : Submodule ℝ E) (u : P) (w : Pᗮ) : ‖(w : E)‖ ≤ ‖(u : E) + (w : E)‖ := by
  have orth : inner ℝ (u : E) (w : E) = 0 := Submodule.inner_right_of_mem_orthogonal u.2 w.2
  have sq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u : E) (w : E) orth
  have : ‖(w : E)‖ * ‖(w : E)‖ ≤ ‖(u : E) + (w : E)‖ * ‖(u : E) + (w : E)‖ := by
    rw [sq]; nlinarith [norm_nonneg (u : E)]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this

theorem leaf_integrable (P : Submodule ℝ E) (g : 𝓢(E, ℂ)) (w : Pᗮ) :
    Integrable (fun u : P => g ((u : E) + (w : E))) := by
  have h := AffineGraphParameter.schwartz_integrable P 0 w g
  refine h.congr (ae_of_all _ fun u => ?_)
  change g (AffineGraphParameter.point P 0 w u) = g ((u : E) + (w : E))
  congr 1
  simp [AffineGraphParameter.point, IntrinsicGraphJacobian.graphDifferential]

/-- One dyadic block paired with a compactly supported Hölder test: the Hölder gain
`r^{-b}` times the supremum of the block's integrals over the leaves `P + w`. -/
theorem block_bound (σ : 𝓢(E, ℂ)) (annulus : ∀ ξ, σ ξ ≠ 0 → 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (χ : ConeDyadicSymbols.RadialCutoff) (P : Submodule ℝ E) {K : Set E} (compact : IsCompact K)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {m : ℕ} (hm : (Module.finrank ℝ Pᗮ : ℝ) < m) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : 𝓢(E, ℂ)) (v : BoundedHolderSpace.graph E b),
      tsupport (BoundedHolderSpace.physical E b v) ⊆ K →
      ∀ (r : ℝ) (hr : 1 ≤ r) (A : ℝ),
      (∀ w : Pᗮ, ∫ u : P, ‖block (dilateSymbol σ r (by linarith)) f ((u : E) + (w : E))‖ ≤ A) →
      ‖∫ x, block (dilateSymbol σ r (by linarith)) f x * BoundedHolderSpace.physical E b v x‖ ≤
        D * ‖v‖ * (r ^ b)⁻¹ * A := by
  let dual := AnnularDualCutoff.symbol (E := E) χ
  have dualZero : dual 0 = 0 := AnnularDualCutoff.collar χ (by rw [norm_zero]; norm_num)
  obtain ⟨B, hB, envelope⟩ := FourierHolderRadialEnvelope.exists_envelope dual dualZero compact
    hb hb1 m
  let I : ℝ := ∫ w : Pᗮ, GraphLeafNorm.radialWeight (m : ℝ) w
  have hI : 0 ≤ I := integral_nonneg fun w => GraphLeafNorm.radialWeight_nonneg _ w
  refine ⟨B * I, mul_nonneg hB hI, ?_⟩
  intro f v support r hr A leaves
  have hr0 : 0 < r := by linarith
  let φ := BoundedHolderSpace.physical E b v
  let g := block (dilateSymbol σ r hr0) f
  let τ := dilateSymbol dual r hr0
  let T : E → ℂ := fun y => ∫ z, kernel τ z * φ (y - z)
  have absorbed : block τ g = g :=
    block_absorb _ _ (dual_absorbs σ annulus χ r hr0) f
  have transpose := pairing_transpose τ (dual_even χ r hr0) g φ
  rw [absorbed] at transpose
  have hT : ∀ x, ‖T x‖ ≤ (B * ‖v‖ * (r ^ b)⁻¹) * GraphLeafNorm.radialWeight (m : ℝ) x :=
    fun x => envelope v support r hr x
  have Tcont : Continuous T := by
    have bdd : BddAbove (range fun x => ‖φ x‖) :=
      ⟨‖φ‖, by rintro _ ⟨x, rfl⟩; exact φ.norm_coe_le_norm x⟩
    have c := bdd.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℂ ℂ)
      (μ := volume) (kernel_integrable τ) φ.continuous
    refine c.congr fun y => ?_
    rw [convolution_def]
    rfl
  have Tbound : ∀ x, ‖T x‖ ≤ B * ‖v‖ * (r ^ b)⁻¹ := fun x =>
    (hT x).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left
      (GraphLeafNorm.radialWeight_le_one (by positivity) x) (by positivity)) (mul_one _))
  have product : Integrable (fun x => g x * T x) :=
    g.integrable.mul_bdd Tcont.aestronglyMeasurable (ae_of_all _ Tbound)
  have pairing := OrthogonalLeafPairing.bound P g T A (B * ‖v‖ * (r ^ b)⁻¹) (by positivity)
    (fun w : Pᗮ => GraphLeafNorm.radialWeight (m : ℝ) w)
    (fun w => GraphLeafNorm.radialWeight_nonneg _ _)
    (GraphLeafNorm.integrable_radialWeight (volume : Measure Pᗮ) hm) product
    (fun w => leaf_integrable P g w) leaves
    (fun u w => (hT _).trans (mul_le_mul_of_nonneg_left
      (GraphLeafNorm.radialWeight_antitone_norm (by positivity) (norm_le_add P u w))
      (by positivity)))
  change ‖∫ x, g x * φ x‖ ≤ B * I * ‖v‖ * (r ^ b)⁻¹ * A
  have eq : (∫ x, g x * φ x) = ∫ x, g x * T x := transpose
  rw [eq]
  calc ‖∫ x, g x * T x‖ ≤ (B * ‖v‖ * (r ^ b)⁻¹ * A) * I := pairing
    _ = B * I * ‖v‖ * (r ^ b)⁻¹ * A := by ring

theorem oblique_norm (P : Submodule ℝ E) (L : P →L[ℝ] Pᗮ) (u : P) (v : Pᗮ) :
    ‖(v : E)‖ ≤ (1 + ‖L‖) * ‖(u : E) + (L u : E) + (v : E)‖ := by
  set x : E := (u : E) + (L u : E) + (v : E)
  have orth : inner ℝ (u : E) ((L u : E) + (v : E)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal u.2 (Pᗮ.add_mem (L u).2 v.2)
  have sq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u : E) ((L u : E) + (v : E)) orth
  have hx : x = (u : E) + ((L u : E) + (v : E)) := by simp only [x, add_assoc]
  have hu : ‖(u : E)‖ ≤ ‖x‖ := by
    have : ‖(u : E)‖ * ‖(u : E)‖ ≤ ‖x‖ * ‖x‖ := by
      rw [hx, sq]; nlinarith [norm_nonneg ((L u : E) + (v : E))]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this
  have hw : ‖(L u : E) + (v : E)‖ ≤ ‖x‖ := by
    have : ‖(L u : E) + (v : E)‖ * ‖(L u : E) + (v : E)‖ ≤ ‖x‖ * ‖x‖ := by
      rw [hx, sq]; nlinarith [norm_nonneg (u : E)]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this
  have hL : ‖(L u : E)‖ ≤ ‖L‖ * ‖x‖ := by
    calc ‖(L u : E)‖ = ‖L u‖ := rfl
      _ ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
      _ = ‖L‖ * ‖(u : E)‖ := rfl
      _ ≤ ‖L‖ * ‖x‖ := mul_le_mul_of_nonneg_left hu (norm_nonneg L)
  have tri : ‖(v : E)‖ ≤ ‖(L u : E) + (v : E)‖ + ‖(L u : E)‖ := by
    calc ‖(v : E)‖ = ‖((L u : E) + (v : E)) - (L u : E)‖ := by rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  nlinarith [norm_nonneg L]

theorem radial_oblique (P : Submodule ℝ E) (L : P →L[ℝ] Pᗮ) (m : ℕ) (u : P) (v : Pᗮ) :
    GraphLeafNorm.radialWeight (m : ℝ) ((u : E) + (L u : E) + (v : E)) ≤
      (1 + ‖L‖) ^ m * GraphLeafNorm.radialWeight (m : ℝ) v := by
  set x : E := (u : E) + (L u : E) + (v : E)
  have h := oblique_norm P L u v
  have hL : 1 ≤ 1 + ‖L‖ := by linarith [norm_nonneg L]
  have base : 1 + ‖v‖ ≤ (1 + ‖L‖) * (1 + ‖x‖) := by
    have : ‖v‖ = ‖(v : E)‖ := rfl
    nlinarith [norm_nonneg x, norm_nonneg L]
  unfold GraphLeafNorm.radialWeight
  have hx0 : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hv0 : 0 < 1 + ‖v‖ := by linarith [norm_nonneg v]
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hv0.le, Real.rpow_natCast, Real.rpow_natCast]
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hv0 m), inv_mul_le_iff₀ (pow_pos hx0 m), ← mul_pow]
  exact pow_le_pow_left₀ hv0.le (by linarith) m

theorem oblique_integrable (P : Submodule ℝ E) (L : P →L[ℝ] Pᗮ) (g : 𝓢(E, ℂ)) (v : Pᗮ) :
    Integrable (fun u : P => g ((u : E) + (L u : E) + (v : E))) := by
  have h := AffineGraphParameter.schwartz_integrable P L v g
  refine h.congr (ae_of_all _ fun u => ?_)
  change g (AffineGraphParameter.point P L v u) = g ((u : E) + (L u : E) + (v : E))
  rfl

/-- Oblique version: leaves `{u + L u + v}` (affine graphs with fixed slope `L`). -/
theorem block_bound_oblique (σ : 𝓢(E, ℂ)) (annulus : ∀ ξ, σ ξ ≠ 0 → 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (χ : ConeDyadicSymbols.RadialCutoff) (P : Submodule ℝ E) (L : P →L[ℝ] Pᗮ) {K : Set E}
    (compact : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {m : ℕ}
    (hm : (Module.finrank ℝ Pᗮ : ℝ) < m) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : 𝓢(E, ℂ)) (v : BoundedHolderSpace.graph E b),
      tsupport (BoundedHolderSpace.physical E b v) ⊆ K →
      ∀ (r : ℝ) (hr : 1 ≤ r) (A : ℝ),
      (∀ w : Pᗮ, ∫ u : P, ‖block (dilateSymbol σ r (by linarith)) f
          ((u : E) + (L u : E) + (w : E))‖ ≤ A) →
      ‖∫ x, block (dilateSymbol σ r (by linarith)) f x * BoundedHolderSpace.physical E b v x‖ ≤
        D * ‖v‖ * (r ^ b)⁻¹ * A := by
  let dual := AnnularDualCutoff.symbol (E := E) χ
  have dualZero : dual 0 = 0 := AnnularDualCutoff.collar χ (by rw [norm_zero]; norm_num)
  obtain ⟨B, hB, envelope⟩ := FourierHolderRadialEnvelope.exists_envelope dual dualZero compact
    hb hb1 m
  let I : ℝ := ∫ w : Pᗮ, GraphLeafNorm.radialWeight (m : ℝ) w
  have hI : 0 ≤ I := integral_nonneg fun w => GraphLeafNorm.radialWeight_nonneg _ w
  have hc : 0 ≤ (1 + ‖L‖) ^ m := pow_nonneg (by linarith [norm_nonneg L]) m
  refine ⟨B * (1 + ‖L‖) ^ m * I, mul_nonneg (mul_nonneg hB hc) hI, ?_⟩
  intro f v support r hr A leaves
  have hr0 : 0 < r := by linarith
  let φ := BoundedHolderSpace.physical E b v
  let g := block (dilateSymbol σ r hr0) f
  let τ := dilateSymbol dual r hr0
  let T : E → ℂ := fun y => ∫ z, kernel τ z * φ (y - z)
  have absorbed : block τ g = g :=
    block_absorb _ _ (dual_absorbs σ annulus χ r hr0) f
  have transpose := pairing_transpose τ (dual_even χ r hr0) g φ
  rw [absorbed] at transpose
  have hT : ∀ x, ‖T x‖ ≤ (B * ‖v‖ * (r ^ b)⁻¹) * GraphLeafNorm.radialWeight (m : ℝ) x :=
    fun x => envelope v support r hr x
  have Tcont : Continuous T := by
    have bdd : BddAbove (range fun x => ‖φ x‖) :=
      ⟨‖φ‖, by rintro _ ⟨x, rfl⟩; exact φ.norm_coe_le_norm x⟩
    have c := bdd.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℂ ℂ)
      (μ := volume) (kernel_integrable τ) φ.continuous
    refine c.congr fun y => ?_
    rw [convolution_def]
    rfl
  have Tbound : ∀ x, ‖T x‖ ≤ B * ‖v‖ * (r ^ b)⁻¹ := fun x =>
    (hT x).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left
      (GraphLeafNorm.radialWeight_le_one (by positivity) x) (by positivity)) (mul_one _))
  have product : Integrable (fun x => g x * T x) :=
    g.integrable.mul_bdd Tcont.aestronglyMeasurable (ae_of_all _ Tbound)
  have pairing := ObliqueLeafPairing.bound P L g T A (B * ‖v‖ * (r ^ b)⁻¹ * (1 + ‖L‖) ^ m)
    (by positivity) (fun w : Pᗮ => GraphLeafNorm.radialWeight (m : ℝ) w)
    (fun w => GraphLeafNorm.radialWeight_nonneg _ _)
    (GraphLeafNorm.integrable_radialWeight (volume : Measure Pᗮ) hm) product
    (fun w => oblique_integrable P L g w) leaves
    (fun u w => (hT _).trans (by
      calc B * ‖v‖ * (r ^ b)⁻¹ * GraphLeafNorm.radialWeight (m : ℝ) ((u : E) + (L u : E) + (w : E))
          ≤ B * ‖v‖ * (r ^ b)⁻¹ * ((1 + ‖L‖) ^ m * GraphLeafNorm.radialWeight (m : ℝ) w) :=
            mul_le_mul_of_nonneg_left (radial_oblique P L m u w) (by positivity)
        _ = B * ‖v‖ * (r ^ b)⁻¹ * (1 + ‖L‖) ^ m * GraphLeafNorm.radialWeight (m : ℝ) w := by
            ring))
  change ‖∫ x, g x * φ x‖ ≤ B * (1 + ‖L‖) ^ m * I * ‖v‖ * (r ^ b)⁻¹ * A
  have eq : (∫ x, g x * φ x) = ∫ x, g x * T x := transpose
  rw [eq]
  calc ‖∫ x, g x * T x‖ ≤ (B * ‖v‖ * (r ^ b)⁻¹ * (1 + ‖L‖) ^ m * A) * I := pairing
    _ = B * (1 + ‖L‖) ^ m * I * ‖v‖ * (r ^ b)⁻¹ * A := by ring

end LeanShared.LowOrderBlockPairing
