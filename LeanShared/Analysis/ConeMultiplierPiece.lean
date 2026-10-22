module
public import LeanShared.Analysis.LeafCommutatorDerivative
public import LeanShared.Analysis.DyadicAntiderivative
public import LeanShared.Analysis.ConeKernelUniformMass

/-! One piece of the multiplier estimate: on a translation-closed leaf family, the commutator of the
dyadic cone block `Q_j` (`j = (n, σ)`) with a Schwartz multiplier `a`, applied to the block `u =
Q_{l,s} f`, has leaf integrals at most `K 2^{-max(n,l)}` times the leaf size of `u`. For `l ≤ n`
this is the first-moment bound; for `l > n` the antiderivatives `u = ∑ ∂_{b_i} G_i` and
integration by parts give `2^{-l}`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap ENNReal
open LineDeriv
namespace LeanShared.ConeMultiplierPiece
open FourierSchwartzKernel ConeFourierBlocks ConeDyadicSymbols LeafCommutator DyadicAntiderivative
  LowOrderChartPairing

variable {E ι A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  {Cplus Cminus : Set E}

theorem lipschitz_of_fderiv (a : 𝓢(E, ℂ)) {D : ℝ} (hD : ∀ y, ‖fderiv ℝ a y‖ ≤ D) (x y : E) :
    ‖a x - a y‖ ≤ D * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun _ _ => a.differentiableAt)
    (fun z _ => hD z) (mem_univ y) (mem_univ x)

theorem comm_eq (σ a u : 𝓢(E, ℂ)) :
    comm (kernel σ) a u = fun x => block σ (mul a u) x - a x * block σ u x := by
  funext x
  rw [block_mul]
  ring

theorem comm_continuous (σ a u : 𝓢(E, ℂ)) : Continuous (comm (kernel σ) a u) := by
  rw [comm_eq]
  exact (block σ (mul a u)).continuous.sub (a.continuous.mul (block σ u).continuous)

theorem comm_sum (K a : 𝓢(E, ℂ)) {κ : Type*} (s : Finset κ) (g : κ → 𝓢(E, ℂ)) (x : E) :
    comm K a ⇑(∑ i ∈ s, g i) x = ∑ i ∈ s, comm K a (g i) x := by
  unfold LeafCommutator.comm
  rw [← integral_finsetSum s (fun i _ => comm_integrable K a (g i) x)]
  congr 1
  funext y
  rw [sum_apply, Finset.mul_sum, Finset.mul_sum]

theorem comm_sub (K a u w : 𝓢(E, ℂ)) (x : E) :
    comm K a ⇑(u - w) x = comm K a u x - comm K a w x := by
  unfold LeafCommutator.comm
  rw [← integral_sub (comm_integrable K a u x) (comm_integrable K a w x)]
  congr 1
  funext y
  rw [sub_apply]
  ring

/-- The leaf supremum of a function on the family. -/
@[expose] def leafSup (family : A → Measure E) (u : E → ℂ) : ℝ≥0∞ :=
  ⨆ c, ∫⁻ x, ‖u x‖ₑ ∂family c

theorem piece_le (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (b : OrthonormalBasis ι ℝ E)
    (family : A → Measure E) [∀ c, SFinite (family c)]
    (translate : ∀ c (z : E), ∃ c', (family c).map (fun x => x + z) = family c')
    (a : 𝓢(E, ℂ)) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ y, ‖fderiv ℝ a y‖ ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E, ℂ)) (j : ℕ × Bool) (l : ℕ) (s : Bool) (c : A),
      (∫⁻ x, ‖comm (kernel (symbols χ Φ j)) a (block (symbols χ Φ (l, s)) f) x‖ₑ ∂family c) ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ (max j.1 l))⁻¹) *
          leafSup family (block (symbols χ Φ (l, s)) f) := by
  obtain ⟨C0, hC0, m1⟩ := ConeKernelMoments.exists_moment_bound χ Φ
  obtain ⟨C1, hC1, m2⟩ := ConeKernelMoments.exists_derivative_moment_bound χ Φ
  obtain ⟨A0, hA0, mass⟩ := exists_uniform_kernel_mass χ Φ
  let H : ι → ℝ := fun i => ∫ z, ‖kernel (symbolAt b χ i) z‖
  have hH : ∀ i, 0 ≤ H i := fun i => integral_nonneg fun z => norm_nonneg _
  let K1 : ℝ := ∑ i, (D * C1 + D * A0) * H i
  have hK1 : 0 ≤ K1 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (add_nonneg (mul_nonneg hD0 hC1) (mul_nonneg hD0 hA0)) (hH i)
  refine ⟨D * C0 + K1, add_nonneg (mul_nonneg hD0 hC0) hK1, ?_⟩
  intro f j l s c
  obtain ⟨n, σ⟩ := j
  have lip := lipschitz_of_fderiv a hD
  have pow_pos' : ∀ m : ℕ, (0 : ℝ) < 2 ^ m := fun m => pow_pos (by norm_num) m
  set S := leafSup family (block (symbols χ Φ (l, s)) f) with hS
  -- the direct (first-moment) bound
  have direct : (∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a
      (block (symbols χ Φ (l, s)) f) x‖ₑ ∂family c) ≤
        ENNReal.ofReal ((D * C0 + K1) * ((2 : ℝ) ^ n)⁻¹) * S := by
    refine (leaf_comm_le (family c) family (translate c) _ a _ hD0 lip).trans ?_
    rw [← ENNReal.ofReal_mul hD0]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc D * ∫ z, ‖z‖ * ‖kernel (symbols χ Φ (n, σ)) z‖ ≤ D * (C0 * ((2 : ℝ) ^ n)⁻¹) :=
          mul_le_mul_of_nonneg_left (m1 (n, σ)) hD0
      _ ≤ (D * C0 + K1) * ((2 : ℝ) ^ n)⁻¹ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK1)
            (inv_nonneg.mpr (pow_pos' n).le)
  rcases le_total l n with hl | hl
  · rw [show max (n, σ).1 l = n from max_eq_left hl]
    exact direct
  · rcases Nat.eq_zero_or_pos l with hl0 | hl0
    · subst hl0
      rw [show max (n, σ).1 0 = n from max_eq_left (Nat.zero_le _)]
      exact direct
    rw [show max (n, σ).1 l = l from max_eq_right hl]
    -- the integration-by-parts bound
    have hr : (0 : ℝ) < 2 ^ l := pow_pos' l
    have hl' : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl0
    set G : ι → 𝓢(E, ℂ) := fun i => antiderivative b χ (highSymbol χ Φ s) (2 ^ l) hr f i
    have decomposition : block (symbols χ Φ (l, s)) f = ∑ i, ∂_{b i} (G i) := by
      rw [symbols_high χ Φ hl' s]
      exact (sum_lineDeriv b χ (highSymbol χ Φ s) (highSymbol_annulus χ Φ s) _ hr f).symm
    have split (x : E) : comm (kernel (symbols χ Φ (n, σ))) a (block (symbols χ Φ (l, s)) f) x =
        ∑ i, comm (kernel (symbols χ Φ (n, σ))) a (fun y => fderiv ℝ (G i) y (b i)) x := by
      rw [decomposition, comm_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : ((∂_{b i} (G i) : 𝓢(E, ℂ)) : E → ℂ) = fun y => fderiv ℝ (G i) y (b i) :=
        funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv (b i) (G i) y
      rw [h]
    have each (i : ι) : (∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a
        (fun y => fderiv ℝ (G i) y (b i)) x‖ₑ ∂family c) ≤
          ENNReal.ofReal ((D * C1 + D * A0) * H i * ((2 : ℝ) ^ l)⁻¹) * S := by
      have leafG : leafSup family (G i) ≤
          ENNReal.ofReal ((2 : ℝ) ^ l)⁻¹ * ENNReal.ofReal (H i) * S := by
        refine iSup_le fun c' => ?_
        have h := leaf_antiderivative_le b χ (family c') family (translate c')
          (highSymbol χ Φ s) (2 ^ l) hr f i
        rw [← symbols_high χ Φ hl' s] at h
        exact h
      have deriv (y : E) : ‖fderiv ℝ a y (b i)‖ ≤ D := by
        refine ((fderiv ℝ a y).le_opNorm (b i)).trans ?_
        rw [b.orthonormal.1 i, mul_one]
        exact hD y
      have massj : ENNReal.ofReal (∫ z, ‖kernel (symbols χ Φ (n, σ)) z‖) ≤ ENNReal.ofReal A0 := by
        rw [← lintegral_mass]
        exact mass (n, σ)
      have massR : ∫ z, ‖kernel (symbols χ Φ (n, σ)) z‖ ≤ A0 :=
        (ENNReal.ofReal_le_ofReal_iff hA0).mp massj
      have hv : ‖b i‖ₑ = 1 := by
        rw [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one]
      refine (leaf_comm_lineDeriv_le (family c) family (translate c) _ a (G i) (b i) hD0
        lip deriv).trans ?_
      rw [hv, mul_one]
      calc (ENNReal.ofReal D * ENNReal.ofReal (∫ z, ‖fderiv ℝ (kernel (symbols χ Φ (n, σ))) z‖ * ‖z‖) +
            ENNReal.ofReal D * ENNReal.ofReal (∫ z, ‖kernel (symbols χ Φ (n, σ)) z‖)) *
            leafSup family (G i)
          ≤ (ENNReal.ofReal D * ENNReal.ofReal C1 + ENNReal.ofReal D * ENNReal.ofReal A0) *
              (ENNReal.ofReal ((2 : ℝ) ^ l)⁻¹ * ENNReal.ofReal (H i) * S) := by
            refine mul_le_mul' (add_le_add (mul_le_mul_right (ENNReal.ofReal_le_ofReal (m2 (n, σ))) _)
              (mul_le_mul_right (ENNReal.ofReal_le_ofReal massR) _)) leafG
          _ = ENNReal.ofReal ((D * C1 + D * A0) * H i * ((2 : ℝ) ^ l)⁻¹) * S := by
            rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg (mul_nonneg hD0 hC1)
              (mul_nonneg hD0 hA0)) (hH i)), ENNReal.ofReal_mul (add_nonneg (mul_nonneg hD0 hC1)
              (mul_nonneg hD0 hA0)), ENNReal.ofReal_add (mul_nonneg hD0 hC1) (mul_nonneg hD0 hA0),
              ENNReal.ofReal_mul hD0, ENNReal.ofReal_mul hD0]
            ring
    have measurable (i : ι) : Measurable (fun x => ‖comm (kernel (symbols χ Φ (n, σ))) a
        (fun y => fderiv ℝ (G i) y (b i)) x‖ₑ) := by
      have h : (fun y => fderiv ℝ (G i) y (b i)) = ((∂_{b i} (G i) : 𝓢(E, ℂ)) : E → ℂ) :=
        funext fun y => (SchwartzMap.lineDerivOp_apply_eq_fderiv (b i) (G i) y).symm
      rw [h]
      exact (comm_continuous _ a _).measurable.enorm
    calc (∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a (block (symbols χ Φ (l, s)) f) x‖ₑ ∂family c)
        ≤ ∫⁻ x, ∑ i, ‖comm (kernel (symbols χ Φ (n, σ))) a
            (fun y => fderiv ℝ (G i) y (b i)) x‖ₑ ∂family c := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [split]
          exact enorm_sum_le _ _
      _ = ∑ i, ∫⁻ x, ‖comm (kernel (symbols χ Φ (n, σ))) a
            (fun y => fderiv ℝ (G i) y (b i)) x‖ₑ ∂family c :=
          lintegral_finsetSum _ fun i _ => measurable i
      _ ≤ ∑ i, ENNReal.ofReal ((D * C1 + D * A0) * H i * ((2 : ℝ) ^ l)⁻¹) * S :=
          Finset.sum_le_sum fun i _ => each i
      _ = ENNReal.ofReal (K1 * ((2 : ℝ) ^ l)⁻¹) * S := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
            (mul_nonneg (add_nonneg (mul_nonneg hD0 hC1) (mul_nonneg hD0 hA0)) (hH i))
            (inv_nonneg.mpr hr.le)), ← Finset.sum_mul]
      _ ≤ ENNReal.ofReal ((D * C0 + K1) * ((2 : ℝ) ^ l)⁻¹) * S := by
          gcongr
          exact le_add_of_nonneg_left (mul_nonneg hD0 hC0)

end LeanShared.ConeMultiplierPiece
