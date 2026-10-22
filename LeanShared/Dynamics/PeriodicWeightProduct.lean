module
public import LeanShared.Dynamics.PeriodicWeightDistortion

/-! Distortion of weight products along a periodic chart chain. For a point of the chain
region whose closing defect is at most `ρ`, the weight product over `N m` steps equals the
weight product at the periodic point times a factor `R` with `exp(-2X) ≤ R ≤ exp X`,
`X = N C_w (bound (C+1) ρ)^q 2/(1 - θ^q)`, uniformly in the period. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric Finset
open scoped Manifold ContDiff Topology NNReal
open LeanShared.HyperbolicBasicSet LeanShared.PeriodicChartConstants
namespace LeanShared.PeriodicChartChains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
  {a : IsometricFraming h} {F : ChartFamily E M} {lam : ℝ} {N : ℕ}

set_option maxHeartbeats 800000 in
theorem weight_product_close {p : Λ} {m : ℕ} {i : F.ι}
    (pc : PeriodicChain a F ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (invariant : ∀ x ∈ Λ, T x ∈ Λ)
    (Rw Cw : ℝ) (hCw : 0 ≤ Cw) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (ratio : ∀ x ∈ Λ, ∀ c : F.ι, x ∈ F.good lam c → ∀ l < N, ∀ v : E, ‖v‖ ≤ Rw →
      |g ((T : M → M)^[l] ((F.chart c).symm (F.chart c x + v))) / g ((T : M → M)^[l] x) - 1| ≤
        Cw * ‖v‖ ^ q)
    (w : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
    (hw : w ∈ (pc.chain.toData δD hδD small').region) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hclose : ‖(pc.chain.toData δD hδD small').closing w‖ ≤ ρ)
    (hR : 2 * (pc.chain.bound * (((pc.chain.toData δD hδD small').constant + 1) * ρ)) ≤ Rw)
    (hhalf : Cw * (2 * (pc.chain.bound * (((pc.chain.toData δD hδD small').constant + 1) * ρ))) ^ q
      ≤ 1 / 2) :
    ∃ R : ℝ, weightProduct T g (N * m) (pc.decode w) = weightProduct T g (N * m) p.val * R ∧
      Real.exp (-(2 * (N * (Cw * (pc.chain.bound * (((pc.chain.toData δD hδD small').constant + 1) *
        ρ)) ^ q) * (2 / (1 - HyperbolicConeCloseness.rate (pc.chain.toData δD hδD small').k
          (pc.chain.toData δD hδD small').δ ^ q))))) ≤ R ∧
      R ≤ Real.exp (N * (Cw * (pc.chain.bound * (((pc.chain.toData δD hδD small').constant + 1) *
        ρ)) ^ q) * (2 / (1 - HyperbolicConeCloseness.rate (pc.chain.toData δD hδD small').k
          (pc.chain.toData δD hδD small').δ ^ q))) := by
  set d := pc.chain.toData δD hδD small'
  set x := pc.decode w
  have HN : ((T ^ N : M ≃ₜ M) : M → M) = (T : M → M)^[N] := DiffeomorphismIterates.coe_pow T N
  have hm : d.period = m := pc.period_eq
  set θ := HyperbolicConeCloseness.rate d.k d.δ
  have hθ0 : 0 ≤ θ := HyperbolicConeCloseness.rate_nonneg _ _ d.k.coe_nonneg d.δ.coe_nonneg
  have hθ1 : θ < 1 := HyperbolicConeCloseness.rate_lt_one _ _ d.k.coe_nonneg d.δ.coe_nonneg
    d.k_add_δ_lt_one
  set B := pc.chain.bound * ((d.constant + 1) * ρ)
  have hB : 0 ≤ B := by
    have := pc.chain.bound_pos
    have := d.constant_nonneg
    positivity
  -- block displacements
  set v : ℕ → E := fun j => F.chart (pc.σ j) (((T ^ N : M ≃ₜ M) : M → M)^[j] x) - F.chart (pc.σ j) (pc.point j).val
  have pointVal (j : ℕ) : (pc.point j).val = ((T ^ N : M ≃ₜ M) : M → M)^[j] p.val := pc.point_val j
  have vBound (j : ℕ) (hj : j < m) : ‖v j‖ ≤ B * (θ ^ j + θ ^ (m - j)) := by
    have eq := (pc.orbit_eq δD hδD small' w hw j hj.le).2
    have value : v j = pc.chain.L j (d.orbit j w) := by
      rw [eq, ContinuousLinearEquiv.apply_symm_apply, pc.a_eq j]
    rw [value]
    have close := d.closeness w hw j (by rw [hm]; exact hj.le)
    rw [hm] at close
    calc ‖pc.chain.L j (d.orbit j w)‖ ≤ pc.chain.bound * ‖d.orbit j w‖ :=
          ((pc.chain.L j).toContinuousLinearMap.le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (pc.chain.L_bound j) (norm_nonneg _))
      _ ≤ pc.chain.bound * ((d.constant + 1) * ‖d.closing w‖ * (θ ^ j + θ ^ (m - j))) :=
          mul_le_mul_of_nonneg_left close pc.chain.bound_pos.le
      _ ≤ pc.chain.bound * ((d.constant + 1) * ρ * (θ ^ j + θ ^ (m - j))) := by
          apply mul_le_mul_of_nonneg_left _ pc.chain.bound_pos.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hclose (by linarith [d.constant_nonneg])
      _ = B * (θ ^ j + θ ^ (m - j)) := by ring
  have decodeIter (j : ℕ) (hj : j < m) :
      (F.chart (pc.σ j)).symm (F.chart (pc.σ j) (pc.point j).val + v j) = ((T ^ N : M ≃ₜ M) : M → M)^[j] x := by
    have source := (pc.orbit_eq δD hδD small' w hw j hj.le).1
    simp only [v, add_sub_cancel]
    exact (F.chart (pc.σ j)).left_inv source
  -- the ratios
  set r : ℕ → ℕ → ℝ := fun j l => g ((T : M → M)^[l] (((T ^ N : M ≃ₜ M) : M → M)^[j] x)) / g ((T : M → M)^[l] (((T ^ N : M ≃ₜ M) : M → M)^[j] p.val))
  set e : ℕ → ℝ := fun j => Cw * ‖v j‖ ^ q
  have vSmall (j : ℕ) (hj : j < m) : ‖v j‖ ≤ 2 * B := by
    refine (vBound j hj).trans ?_
    have : θ ^ j + θ ^ (m - j) ≤ 2 := by
      have := pow_le_one₀ hθ0 hθ1.le (n := j)
      have := pow_le_one₀ hθ0 hθ1.le (n := m - j)
      linarith
    nlinarith
  have rClose (j : ℕ) (hj : j < m) (l : ℕ) (hl : l < N) : |r j l - 1| ≤ e j := by
    have := ratio (pc.point j).val (pc.point j).property (pc.σ j) (pc.good j) l hl (v j)
      ((vSmall j hj).trans hR)
    rwa [decodeIter j hj, pointVal j] at this
  have eHalf (j : ℕ) (hj : j < m) : e j ≤ 1 / 2 := by
    refine le_trans ?_ hhalf
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (vSmall j hj) hq.le) hCw
  have e0 (j : ℕ) : 0 ≤ e j := mul_nonneg hCw (Real.rpow_nonneg (norm_nonneg _) _)
  -- products
  have gpos (j l : ℕ) : 0 < g ((T : M → M)^[l] (((T ^ N : M ≃ₜ M) : M → M)^[j] p.val)) := by
    apply positive
    have all : ∀ n : ℕ, ∀ y ∈ Λ, (T : M → M)^[n] y ∈ Λ := by
      intro n
      induction n with
      | zero => intro y hy; exact hy
      | succ n ih => intro y hy; rw [Function.iterate_succ_apply']; exact invariant _ (ih y hy)
    rw [HN, ← Function.iterate_mul]
    exact all _ _ (all _ _ p.property)
  have split (z : M) : weightProduct T g (N * m) z =
      ∏ j ∈ range m, ∏ l ∈ range N, g ((T : M → M)^[l] (((T ^ N : M ≃ₜ M) : M → M)^[j] z)) := by
    rw [weightProduct_blocks, HN]
  set R := ∏ j ∈ range m, ∏ l ∈ range N, r j l
  refine ⟨R, ?_, ?_⟩
  · rw [split, split, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun l _ => ?_
    simp only [r]
    field_simp [(gpos j l).ne']
  -- bounds on R
  have sumE : ∑ j ∈ range m, ∑ l ∈ range N, e j ≤
      N * (Cw * B ^ q) * (2 / (1 - θ ^ q)) := by
    have hq' : 0 ≤ θ ^ q := Real.rpow_nonneg hθ0 _
    have hq1' : θ ^ q < 1 := Real.rpow_lt_one hθ0 hθ1 hq
    have each (j : ℕ) (hj : j ∈ range m) :
        ∑ l ∈ range N, e j ≤ N * (Cw * B ^ q) * ((θ ^ q) ^ j + (θ ^ q) ^ (m - j)) := by
      rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hvj := vBound j (mem_range.mp hj)
      calc e j = Cw * ‖v j‖ ^ q := rfl
        _ ≤ Cw * (B * (θ ^ j + θ ^ (m - j))) ^ q :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hvj hq.le) hCw
        _ = Cw * (B ^ q * (θ ^ j + θ ^ (m - j)) ^ q) := by
            rw [Real.mul_rpow hB (by positivity)]
        _ ≤ Cw * (B ^ q * ((θ ^ j) ^ q + (θ ^ (m - j)) ^ q)) := by
            apply mul_le_mul_of_nonneg_left _ hCw
            exact mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow (by positivity)
              (by positivity) hq.le hq1) (Real.rpow_nonneg hB _)
        _ = Cw * B ^ q * ((θ ^ q) ^ j + (θ ^ q) ^ (m - j)) := by
            rw [← Real.rpow_natCast_mul hθ0, ← Real.rpow_natCast_mul hθ0, mul_comm (j : ℝ),
              mul_comm ((m - j : ℕ) : ℝ), Real.rpow_mul_natCast hθ0, Real.rpow_mul_natCast hθ0]
            ring
    calc ∑ j ∈ range m, ∑ l ∈ range N, e j
        ≤ ∑ j ∈ range m, N * (Cw * B ^ q) * ((θ ^ q) ^ j + (θ ^ q) ^ (m - j)) := sum_le_sum each
      _ = N * (Cw * B ^ q) * ∑ j ∈ range m, ((θ ^ q) ^ j + (θ ^ q) ^ (m - j)) := by
          rw [mul_sum]
      _ ≤ N * (Cw * B ^ q) * (2 / (1 - θ ^ q)) :=
          mul_le_mul_of_nonneg_left (LocalPeriodicClosing.Data.geometric_two _ hq' hq1' m)
            (by have := Real.rpow_nonneg hB q; positivity)
  have flat : R = ∏ jl ∈ range m ×ˢ range N, r jl.1 jl.2 := by
    rw [prod_product]
  have flatSum : ∑ j ∈ range m, ∑ l ∈ range N, e j = ∑ jl ∈ range m ×ˢ range N, e jl.1 := by
    rw [sum_product]
  have bounds := DeterminantNearOne.prod_bounds (range m ×ˢ range N) (fun jl => r jl.1 jl.2)
    (fun jl => e jl.1) (fun jl _ => e0 _)
    (fun jl hjl => eHalf _ (mem_range.mp (mem_product.mp hjl).1))
    (fun jl hjl => rClose _ (mem_range.mp (mem_product.mp hjl).1) _
      (mem_range.mp (mem_product.mp hjl).2))
  rw [← flat, ← flatSum] at bounds
  constructor
  · refine le_trans ?_ bounds.1
    apply Real.exp_le_exp.mpr
    linarith
  · exact bounds.2.trans (Real.exp_le_exp.mpr sumE)

end LeanShared.PeriodicChartChains
