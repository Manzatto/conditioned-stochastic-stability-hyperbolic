module
public import LeanShared.Analysis.ConeMultiplierPiece
public import LeanShared.Analysis.ConeMultiplierSeries
public import LeanShared.Analysis.SchwartzAmbientLeafEntry
public import LeanShared.Analysis.ConeFourierUniformResolution

/-! Bounded multiplication on the cone block norm. For the fixed dyadic cone blocks and a
translation-closed leaf family, multiplication by a Schwartz function `a` is bounded on the
block core norm when the exponents satisfy `t(σ) - 1 - t(s) < 0`, `t(s) > -1` and `t(σ) ≤ 1`:
`Q_j (a f) = a Q_j f + [Q_j, a] f`, the commutator is the pointwise limit of its values on the
dyadic partial sums (Fourier-uniform resolution), Fatou passes the piece bounds `K 2^{-max(n,l)}
2^{-t(s) l} ‖f‖` to the limit, and the dyadic series is bounded uniformly in `n`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal Topology FourierTransform
namespace LeanShared.ConeMultiplierBound
open FourierSchwartzKernel ConeFourierBlocks ConeDyadicSymbols LeafCommutator ConeMultiplierPiece
  ConeFourierPairingResolution SchwartzJetSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus : Set E}

/-- The commutator is controlled by the Fourier mass of its input. -/
theorem comm_norm_le (K a g : 𝓢(E, ℂ)) {Ca : ℝ} (hCa : ∀ y, ‖a y‖ ≤ Ca) (x : E) :
    ‖comm K a g x‖ ≤ (∫ z, ‖K z‖) * (2 * Ca * ∫ ξ, ‖(𝓕 g) ξ‖) := by
  have hg : ∀ y, ‖g y‖ ≤ ∫ ξ, ‖(𝓕 g) ξ‖ := ConeFourierUniformResolution.norm_le_integral_fourier g
  have hG : 0 ≤ ∫ ξ, ‖(𝓕 g) ξ‖ := integral_nonneg fun ξ => norm_nonneg _
  have bound : ∀ y, ‖K (x - y) * ((a y - a x) * g y)‖ ≤ ‖K (x - y)‖ * (2 * Ca * ∫ ξ, ‖(𝓕 g) ξ‖) :=
    fun y => by
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have ha : ‖a y - a x‖ ≤ 2 * Ca := by linarith [norm_sub_le (a y) (a x), hCa y, hCa x]
      exact mul_le_mul ha (hg y) (norm_nonneg _) ((norm_nonneg _).trans ha)
  have integrable : Integrable (fun y => ‖K (x - y)‖ * (2 * Ca * ∫ ξ, ‖(𝓕 g) ξ‖)) :=
    ((K.integrable.comp_sub_left x).norm).mul_const _
  refine (norm_integral_le_of_norm_le integrable (ae_of_all _ bound)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_sub_left_eq_self (fun z => ‖K z‖) volume x]

/-- The commutator on the dyadic partial sums is the finite sum of its pieces. -/
theorem comm_partialSum (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (K a f : 𝓢(E, ℂ))
    (N : ℕ) (x : E) :
    comm K a (partialSum χ Φ N f) x =
      ∑ l ∈ Finset.range (N + 1), ∑ s : Bool, comm K a (block (symbols χ Φ (l, s)) f) x := by
  rw [partialSum, comm_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [comm_sum]

/-- The commutator is the pointwise limit along the dyadic partial sums. -/
theorem comm_tendsto (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (K a f : 𝓢(E, ℂ))
    (x : E) :
    Tendsto (fun N => comm K a (partialSum χ Φ N f) x) atTop (𝓝 (comm K a f x)) := by
  obtain ⟨Ca, hCa⟩ := exists_bound a
  have small := ConeFourierUniformResolution.uniform χ Φ f
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK : 0 ≤ ∫ z, ‖K z‖ := integral_nonneg fun z => norm_nonneg _
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0)
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (?_ : Tendsto
    (fun N => (∫ z, ‖K z‖) * (2 * Ca * ∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖)) atTop (𝓝 0))
  · rw [← comm_sub]
    exact comm_norm_le K a _ hCa x
  · have h := (small.const_mul (2 * Ca)).const_mul (∫ z, ‖K z‖)
    simpa only [mul_zero] using h

theorem block_component_norm {U A S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U]
    (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
    (leaves : A → GraphLeafNorm.GraphLeaf U E J) (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ))
    (g : supportedCore D) (j : ℕ × S) (c : A) :
    ‖SchwartzAmbientBlocks.block μ hJ leaves D σ j g c‖ =
      ∫ x, ‖block (σ j) g.val x‖ ∂(leaves c).measure μ := by
  have hae := SchwartzAmbientRealization.realization_ae μ hJ leaves (block (σ j) g.val) c
  change ‖(SchwartzAmbientRealization.realization μ hJ leaves (block (σ j) g.val)) c‖ = _
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])

theorem exponent_identity (e q : ℝ) (n l : ℕ) :
    ((2 : ℝ) ^ (max n l))⁻¹ * ((2 : ℝ) ^ (q * l))⁻¹ =
      ((2 : ℝ) ^ (e * n))⁻¹ * (2 : ℝ) ^ (e * n - (max n l : ℕ) - q * l) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_sub h2, Real.rpow_sub h2, Real.rpow_natCast]
  field_simp

section Main
variable {U A : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J) (D : Set E)
  (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (t : Bool → ℝ)
  (bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D (symbols χ Φ) t)

/-- The leaf supremum of a block of a core function is controlled by its core norm. -/
theorem leafSup_block_le (f : supportedCore D) (l : ℕ) (s : Bool) :
    leafSup (fun c => (leaves c).measure μ) (block (symbols χ Φ (l, s)) f.val) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (t s * l))⁻¹ *
        ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D (symbols χ Φ) t bounded f‖) := by
  refine iSup_le fun c => ?_
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (SchwartzAmbientRealization.integrable μ leaves _ c)]
  exact ENNReal.ofReal_le_ofReal
    (SchwartzAmbientLeafEntry.leaf_le_core μ hJ leaves D (symbols χ Φ) t bounded f (l, s) c)

/-- The Fatou bound for the commutator on one leaf. -/
theorem leaf_comm_le_of_pieces (ν : Measure E) (K a f : 𝓢(E, ℂ)) (σ : 𝓢(E, ℂ)) {B : ℝ≥0∞}
    (hK : K = kernel σ)
    (pieces : ∀ N, (∑ l ∈ Finset.range (N + 1), ∑ s : Bool,
      ∫⁻ x, ‖comm K a (block (symbols χ Φ (l, s)) f) x‖ₑ ∂ν) ≤ B) :
    (∫⁻ x, ‖comm K a f x‖ₑ ∂ν) ≤ B := by
  subst hK
  have limit (x : E) : liminf (fun N => ‖comm (kernel σ) a (partialSum χ Φ N f) x‖ₑ) atTop =
      ‖comm (kernel σ) a f x‖ₑ :=
    ((comm_tendsto χ Φ (kernel σ) a f x).enorm).liminf_eq
  have each (N : ℕ) : (∫⁻ x, ‖comm (kernel σ) a (partialSum χ Φ N f) x‖ₑ ∂ν) ≤ B := by
    refine le_trans ?_ (pieces N)
    calc (∫⁻ x, ‖comm (kernel σ) a (partialSum χ Φ N f) x‖ₑ ∂ν)
        ≤ ∫⁻ x, ∑ l ∈ Finset.range (N + 1), ∑ s : Bool,
            ‖comm (kernel σ) a (block (symbols χ Φ (l, s)) f) x‖ₑ ∂ν := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [comm_partialSum]
          refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => enorm_sum_le _ _)
      _ = _ := by
          rw [lintegral_finsetSum _ fun l _ => Finset.measurable_sum _ fun s _ =>
            (comm_continuous _ a _).measurable.enorm]
          refine Finset.sum_congr rfl fun l _ => ?_
          exact lintegral_finsetSum _ fun s _ => (comm_continuous _ a _).measurable.enorm
  calc (∫⁻ x, ‖comm (kernel σ) a f x‖ₑ ∂ν)
      = ∫⁻ x, liminf (fun N => ‖comm (kernel σ) a (partialSum χ Φ N f) x‖ₑ) atTop ∂ν := by
        congr 1
        funext x
        exact (limit x).symm
    _ ≤ liminf (fun N => ∫⁻ x, ‖comm (kernel σ) a (partialSum χ Φ N f) x‖ₑ ∂ν) atTop :=
        lintegral_liminf_le fun N => (comm_continuous _ a _).measurable.enorm
    _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall each)

/-- Multiplication by a Schwartz function is bounded on the cone block core norm. -/
theorem multiplier_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    (h1 : ∀ σ s, t σ - 1 - t s < 0) (h2 : ∀ s, -1 - t s < 0) (h3 : ∀ σ, t σ ≤ 1)
    (a : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : supportedCore D, g.val = mul a f.val →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D (symbols χ Φ) t bounded g‖ ≤
        C * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D (symbols χ Φ) t bounded f‖ := by
  obtain ⟨Ca, hCa⟩ := exists_bound a
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0)
  obtain ⟨Dd, hDd⟩ := exists_fderiv_bound a
  have hD0 : 0 ≤ Dd := (norm_nonneg _).trans (hDd 0)
  let family : A → Measure E := fun c => (leaves c).measure μ
  obtain ⟨K, hK, piece⟩ := piece_le χ Φ (stdOrthonormalBasis ℝ E) family translate a hD0 hDd
  have hB : ∀ σ s, 0 ≤ ConeMultiplierSeries.bound (t σ) (t s) := fun σ s =>
    ConeMultiplierSeries.bound_nonneg _ _ (h1 σ s) (h2 s)
  let Bt : ℝ := ∑ σ : Bool, ∑ s : Bool, ConeMultiplierSeries.bound (t σ) (t s)
  have hBt : 0 ≤ Bt := Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun s _ => hB σ s
  refine ⟨Ca + K * Bt, add_nonneg hCa0 (mul_nonneg hK hBt), ?_⟩
  intro f g hg
  set A0 := ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D (symbols χ Φ) t bounded f‖ with hA0def
  have hA0 : 0 ≤ A0 := norm_nonneg _
  rw [SchwartzAmbientBlocks.coreMap_norm]
  refine ciSup_le fun j => ?_
  obtain ⟨n, σ⟩ := j
  have pow_pos' : (0 : ℝ) < (2 : ℝ) ^ (t σ * n) := Real.rpow_pos_of_pos (by norm_num) _
  set Bσ : ℝ := ∑ s : Bool, ConeMultiplierSeries.bound (t σ) (t s) with hBσ
  have hBσ0 : 0 ≤ Bσ := Finset.sum_nonneg fun s _ => hB σ s
  have hBσle : Bσ ≤ Bt :=
    Finset.single_le_sum (f := fun σ : Bool => ∑ s : Bool, ConeMultiplierSeries.bound (t σ) (t s))
      (fun σ _ => Finset.sum_nonneg fun s _ => hB σ s) (Finset.mem_univ σ)
  -- the commutator on every leaf
  have commLeaf (c : A) : (∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a f.val x‖ₑ ∂family c) ≤
      ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ * Bσ) := by
    refine leaf_comm_le_of_pieces χ Φ (family c) _ a f.val (symbols χ Φ (n, σ)) rfl fun N => ?_
    have term (l : ℕ) (s : Bool) :
        (∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a (block (symbols χ Φ (l, s)) f.val) x‖ₑ
          ∂family c) ≤ ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ *
            (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l)) := by
      refine (piece f.val (n, σ) l s c).trans ?_
      refine (mul_le_mul_right (leafSup_block_le μ hJ leaves D χ Φ t bounded f l s) _).trans ?_
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (inv_nonneg.mpr (pow_pos (by norm_num) _).le))]
      apply le_of_eq
      congr 1
      have identity := exponent_identity (t σ) (t s) n l
      change K * ((2 : ℝ) ^ (max n l))⁻¹ * (((2 : ℝ) ^ (t s * l))⁻¹ * A0) = _
      calc K * ((2 : ℝ) ^ (max n l))⁻¹ * (((2 : ℝ) ^ (t s * l))⁻¹ * A0)
          = K * A0 * (((2 : ℝ) ^ (max n l))⁻¹ * ((2 : ℝ) ^ (t s * l))⁻¹) := by ring
        _ = _ := by rw [identity]; ring
    have nonneg (l : ℕ) (s : Bool) : 0 ≤ K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ *
        (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l) :=
      mul_nonneg (mul_nonneg (mul_nonneg hK hA0) (inv_nonneg.mpr pow_pos'.le))
        (Real.rpow_nonneg (by norm_num) _)
    calc (∑ l ∈ Finset.range (N + 1), ∑ s : Bool,
          ∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a (block (symbols χ Φ (l, s)) f.val) x‖ₑ
            ∂family c)
        ≤ ∑ l ∈ Finset.range (N + 1), ∑ s : Bool, ENNReal.ofReal (K * A0 *
            ((2 : ℝ) ^ (t σ * n))⁻¹ * (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l)) :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun s _ => term l s
      _ = ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ * ∑ s : Bool,
            ∑ l ∈ Finset.range (N + 1), (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l)) := by
          have inner (l : ℕ) : (∑ s : Bool, ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ *
              (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l))) = ENNReal.ofReal (∑ s : Bool,
                K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ * (2 : ℝ) ^ (t σ * n - (max n l : ℕ) - t s * l)) :=
            (ENNReal.ofReal_sum_of_nonneg fun s _ => nonneg l s).symm
          simp_rw [inner]
          rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => Finset.sum_nonneg fun s _ => nonneg l s]
          congr 1
          rw [Finset.sum_comm, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ * Bσ) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hK hA0)
            (inv_nonneg.mpr pow_pos'.le))
          exact Finset.sum_le_sum fun s _ =>
            ConeMultiplierSeries.sum_le (t σ) (t s) (h1 σ s) (h2 s) (h3 σ) n N
  -- the whole block on every leaf
  have leaf (c : A) : (∫ x, ‖block (symbols χ Φ (n, σ)) g.val x‖ ∂family c) ≤
      ((2 : ℝ) ^ (t σ * n))⁻¹ * ((Ca + K * Bσ) * A0) := by
    have split (x : E) : ‖block (symbols χ Φ (n, σ)) g.val x‖ₑ ≤
        ENNReal.ofReal Ca * ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ +
          ‖comm (kernel (symbols χ Φ (n, σ))) a f.val x‖ₑ := by
      rw [hg, block_mul]
      refine (enorm_add_le _ _).trans (add_le_add_left ?_ _)
      rw [enorm_mul, ← ofReal_norm]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCa x)) _
    have first : (∫⁻ x, ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ ∂family c) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (t σ * n))⁻¹ * A0) :=
      (le_iSup (fun c => ∫⁻ x, ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ ∂family c) c).trans
        (leafSup_block_le μ hJ leaves D χ Φ t bounded f n σ)
    have total : (∫⁻ x, ‖block (symbols χ Φ (n, σ)) g.val x‖ₑ ∂family c) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (t σ * n))⁻¹ * ((Ca + K * Bσ) * A0)) := by
      calc (∫⁻ x, ‖block (symbols χ Φ (n, σ)) g.val x‖ₑ ∂family c)
          ≤ ∫⁻ x, (ENNReal.ofReal Ca * ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ +
              ‖comm (kernel (symbols χ Φ (n, σ))) a f.val x‖ₑ) ∂family c := lintegral_mono split
        _ = ENNReal.ofReal Ca * (∫⁻ x, ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ ∂family c) +
              ∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a f.val x‖ₑ ∂family c := by
            rw [lintegral_add_left (f := fun x => ENNReal.ofReal Ca *
                ‖block (symbols χ Φ (n, σ)) f.val x‖ₑ) (measurable_const.mul
              (block (symbols χ Φ (n, σ)) f.val).continuous.measurable.enorm),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Ca * ENNReal.ofReal (((2 : ℝ) ^ (t σ * n))⁻¹ * A0) +
              ENNReal.ofReal (K * A0 * ((2 : ℝ) ^ (t σ * n))⁻¹ * Bσ) :=
            add_le_add (mul_le_mul_right first _) (commLeaf c)
        _ = _ := by
            rw [← ENNReal.ofReal_mul hCa0, ← ENNReal.ofReal_add
              (mul_nonneg hCa0 (mul_nonneg (inv_nonneg.mpr pow_pos'.le) hA0))
              (mul_nonneg (mul_nonneg (mul_nonneg hK hA0) (inv_nonneg.mpr pow_pos'.le)) hBσ0)]
            congr 1
            ring
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (SchwartzAmbientRealization.integrable μ leaves _ c)] at total
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr pow_pos'.le)
      (mul_nonneg (add_nonneg hCa0 (mul_nonneg hK hBσ0)) hA0))).mp total
  -- the weighted block
  have blockNorm : ‖SchwartzAmbientBlocks.block μ hJ leaves D (symbols χ Φ) (n, σ) g‖ ≤
      ((2 : ℝ) ^ (t σ * n))⁻¹ * ((Ca + K * Bσ) * A0) := by
    refine lp.norm_le_of_forall_le (mul_nonneg (inv_nonneg.mpr pow_pos'.le)
      (mul_nonneg (add_nonneg hCa0 (mul_nonneg hK hBσ0)) hA0)) fun c => ?_
    rw [block_component_norm]
    exact leaf c
  have weighted : ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D (symbols χ Φ) t (n, σ) g‖ =
      (2 : ℝ) ^ (t σ * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D (symbols χ Φ) (n, σ) g‖ := by
    change ‖(SchwartzAmbientBlocks.weight t (n, σ) •
      SchwartzAmbientBlocks.block μ hJ leaves D (symbols χ Φ) (n, σ)) g‖ = _
    rw [LinearMap.smul_apply, norm_smul, SchwartzAmbientLeafEntry.weight_norm]
  rw [weighted]
  calc (2 : ℝ) ^ (t σ * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D (symbols χ Φ) (n, σ) g‖
      ≤ (2 : ℝ) ^ (t σ * n) * (((2 : ℝ) ^ (t σ * n))⁻¹ * ((Ca + K * Bσ) * A0)) :=
        mul_le_mul_of_nonneg_left blockNorm pow_pos'.le
    _ = (Ca + K * Bσ) * A0 := by rw [← mul_assoc, mul_inv_cancel₀ pow_pos'.ne', one_mul]
    _ ≤ (Ca + K * Bt) * A0 :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hBσle hK)) hA0

end Main

end LeanShared.ConeMultiplierBound
