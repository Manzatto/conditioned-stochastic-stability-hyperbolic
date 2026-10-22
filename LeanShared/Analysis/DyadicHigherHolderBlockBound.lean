module
public import LeanShared.Analysis.SchwartzSupportedConvolutionLeafBound
public import LeanShared.Analysis.FourierHigherHolderLeafBound
public import LeanShared.Analysis.SchwartzAmbientBlocks
public import LeanShared.Analysis.DyadicSymbols

/-! An actual lower Hölder graph norm controls every weighted physical
Fourier/leaf block whenever both anisotropic exponents are below that order. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction BigOperators Topology
namespace LeanShared.DyadicHigherHolderBlockBound
variable {E : Type} {U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype S]
  {ι:Type} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

include b in
theorem exists_bound (low high : S → 𝓢(E,ℂ)) (zero : ∀s, ∀ᶠ ξ in 𝓝 (0:E), high s ξ=0)
    {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1:a<1) (n:ℕ)
    (t : S → ℝ) (margin : ∀s,t s≤a+(n+1:ℕ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : 𝓢(E,ℂ)) (v : (HigherDerivativeHolderSpace.constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).carrier),
      (∀x, (HigherDerivativeHolderSpace.constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).physical v x=f x) →
      ∀support : tsupport f⊆K, ∀j : ℕ×S,
      ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves K
        (DyadicSymbols.symbol low high) t j ⟨f, fun _ hx => image_eq_zero_of_notMem_tsupport (fun hs => hx (support hs))⟩‖ ≤ C*‖v‖ := by
  classical
  choose L hL lowBound using fun s =>
    SchwartzSupportedConvolutionEnvelope.exists_bcf_leaf_bound μ hJ leaves (low s) compact
  choose H hH highBound using fun s =>
    FourierHigherHolderLeafBound.exists_bound b μ hJ leaves (high s) (zero s) compact ha ha1 n
  let C : ℝ := ∑ s, (L s + H s)
  have hC : 0≤C := Finset.sum_nonneg (fun s _ => add_nonneg (hL s) (hH s))
  have leL (s : S) : L s≤C := (le_add_of_nonneg_right (hH s)).trans
    (Finset.single_le_sum (fun i _ => add_nonneg (hL i) (hH i)) (Finset.mem_univ s))
  have leH (s : S) : H s≤C := (le_add_of_nonneg_left (hL s)).trans
    (Finset.single_le_sum (fun i _ => add_nonneg (hL i) (hH i)) (Finset.mem_univ s))
  refine ⟨C,hC,?_⟩
  intro f v physical support j
  by_cases small : j.1=0
  · have physicalNorm : ‖(HigherDerivativeHolderSpace.constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).physical v‖≤‖v‖ :=
      (HigherDerivativeHolderSpace.constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).physical_norm_le v
    have lowRaw := lowBound j.2 f ((HigherDerivativeHolderSpace.constructFull (E:=E) (F:=ℂ) ha ha1 (n+1)).physical v) physical support
    have blockBound := (lowRaw.trans (mul_le_mul_of_nonneg_left physicalNorm (hL j.2))).trans
      (mul_le_mul_of_nonneg_right (leL j.2) (norm_nonneg v))
    change ‖SchwartzAmbientBlocks.weight t j •
      SchwartzAmbientRealization.realization μ hJ leaves
        (ConeFourierBlocks.block (DyadicSymbols.symbol low high j) f)‖ ≤ _
    have symbolEq : DyadicSymbols.symbol low high j=low j.2 := by
      simp only [DyadicSymbols.symbol, small, ite_true]
    have weightEq : SchwartzAmbientBlocks.weight t j=1 := by
      simp only [SchwartzAmbientBlocks.weight, small, Nat.cast_zero, mul_zero,
        Real.rpow_zero, Complex.ofReal_one]
    rw [symbolEq, weightEq, one_smul]
    exact blockBound
  · have large : 1≤(2:ℝ)^j.1 := one_le_pow₀ (by norm_num)
    have blockBound := highBound j.2 f v physical support ((2:ℝ)^j.1) large
    have growth : (2:ℝ)^(t j.2*(j.1:ℝ)) * (((2:ℝ)^j.1)^(a+(n+1:ℕ)))⁻¹ ≤ 1 := by
      apply (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (pow_pos (by norm_num) _) _)).mpr
      rw [one_mul, ←Real.rpow_natCast_mul (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [margin j.2, (Nat.cast_nonneg j.1 : (0:ℝ)≤(j.1:ℝ))]
    have weighted := mul_le_mul_of_nonneg_left blockBound
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (t j.2*(j.1:ℝ)))
    have estimate : (2:ℝ)^(t j.2*(j.1:ℝ)) *
        ‖SchwartzAmbientRealization.realization μ hJ leaves
          (ConeFourierBlocks.block (FourierSchwartzKernel.dilateSymbol (high j.2)
            ((2:ℝ)^j.1) (pow_pos (by norm_num) _)) f)‖ ≤ C*‖v‖ := by
      calc
        _ ≤ H j.2*‖v‖*((2:ℝ)^(t j.2*(j.1:ℝ))*(((2:ℝ)^j.1)^(a+(n+1:ℕ)))⁻¹) :=
          weighted.trans_eq (by ring)
        _ ≤ H j.2*‖v‖ := mul_le_of_le_one_right (mul_nonneg (hH _) (norm_nonneg _)) growth
        _ ≤ _ := mul_le_mul_of_nonneg_right (leH j.2) (norm_nonneg _)
    change ‖SchwartzAmbientBlocks.weight t j •
      SchwartzAmbientRealization.realization μ hJ leaves
        (ConeFourierBlocks.block (DyadicSymbols.symbol low high j) f)‖ ≤ _
    rw [norm_smul, SchwartzAmbientBlocks.weight, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    simpa only [DyadicSymbols.symbol, small, ite_false] using estimate
end LeanShared.DyadicHigherHolderBlockBound
