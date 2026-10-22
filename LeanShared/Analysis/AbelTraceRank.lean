module
public import LeanShared.Analysis.AbelTraceLaurent
public import LeanShared.Analysis.AbelTraceMeans
public import LeanShared.Analysis.RegularizedTraceFunctional
public import LeanShared.Analysis.SpectralRadiusNeumannSeries
public import Mathlib.Topology.Algebra.Polynomial
public import LeanShared.Analysis.StrongFiniteSpectralTrace

/-! Peripheral ranks from regularized traces, by Abel means at one spectral point.
Let `B` have spectral radius at most one and let `γ` be a unit complex number with a
stable topological Fitting splitting for `B - γ`. If regularized traces `τ_j(B^k)` stay
within `δ_j → 0` of a sequence tending to one, and the smoothings converge weakly on the
generalized kernel, then the generalized kernel has dimension one for `γ = 1` and zero
otherwise. Along `w = γ s`, `s ↓ 1`, the Abel mean of the traces is `(w - γ) τ(R(w))`;
the finite Laurent expansion makes it a polynomial in `(w - γ)⁻¹` up to `O(s - 1)`,
boundedness kills the polar part, and the constant term is `τ(P)`. No power bound,
semisimplicity or global spectral decomposition is assumed. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Filter Finset Set Metric ContinuousLinearMap Submodule
open scoped Topology NNReal ENNReal
namespace LeanShared.AbelTraceRank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

theorem eventually_close (c : ℝ) (hc : 0 < c) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ), 1 < s ∧ s - 1 < c := by
  have h : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
  rw [sub_self] at h
  filter_upwards [(h.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hc),
    self_mem_nhdsWithin] with s h1 h2 using ⟨h2, h1⟩

theorem norm_ray (γ : ℂ) (unit : ‖γ‖ = 1) (s : ℝ) (hs : 1 < s) :
    ‖(γ * s : ℂ)‖ = s ∧ ‖(γ * s - γ : ℂ)‖ = s - 1 := by
  constructor
  · rw [norm_mul, unit, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · rw [show (γ * s - γ : ℂ) = γ * ((s - 1 : ℝ) : ℂ) by push_cast; ring, norm_mul, unit,
      one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- The Abel argument: the regularized trace of the Fitting projection is within `δ_j`
of `1` (for `γ = 1`) or `0`. -/
theorem trace_close (B : E →L[ℂ] E) (radius : spectralRadius ℂ B ≤ 1) (γ : ℂ) (unit : ‖γ‖ = 1)
    (n : ℕ) (compl : IsTopCompl ((B - γ • 1) ^ n).ker ((B - γ • 1) ^ n).range)
    (hker : ((B - γ • 1) ^ (n + 1)).ker = ((B - γ • 1) ^ n).ker)
    (hrange : ((B - γ • 1) ^ (n + 1)).range = ((B - γ • 1) ^ n).range)
    {ι : Type*} (F : ι → RegularizedTraceFunctional.Family E Y)
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop, ‖(F j).traceL (B ^ k) - t k‖ ≤ δ j) (j : ι) :
    ‖(F j).traceL (((B - γ • 1) ^ n).ker.projectionL ((B - γ • 1) ^ n).range compl) -
      (if γ = 1 then 1 else 0)‖ ≤ δ j := by
  set S := B - γ • (1 : E →L[ℂ] E) with hS
  set P := (S ^ n).ker.projectionL (S ^ n).range compl with hP
  set e : ℂ := if γ = 1 then 1 else 0 with he
  obtain ⟨M, ρ, hρ, lau⟩ := AbelTraceLaurent.laurent B γ n compl hker hrange
  set τ := (F j).traceL with hτ
  set C : ℝ := ‖τ‖ * |M| + 1 with hC
  have C0 : 0 < C := by positivity
  have resolventMem (s : ℝ) (hs : 1 < s) : (γ * s : ℂ) ∈ resolventSet ℂ B := by
    refine spectrum.mem_resolventSet_of_spectralRadius_lt (radius.trans_lt ?_)
    rw [ENNReal.one_lt_coe_iff, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      (norm_ray γ unit s hs).1]
    exact hs
  have series (s : ℝ) (hs : 1 < s) :
      HasSum (fun k => AbelTraceMeans.coef γ s k * τ (B ^ k))
        ((γ * s - γ) * τ (resolvent B (γ * s))) := by
    have outside : spectralRadius ℂ B < (‖(γ * s : ℂ)‖₊ : ℝ≥0∞) := by
      refine radius.trans_lt ?_
      rw [ENNReal.one_lt_coe_iff, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
        (norm_ray γ unit s hs).1]
      exact hs
    have h := ((SpectralRadiusNeumannSeries.hasSum B (γ * s) outside).mapL τ).mul_left
      (γ * s - γ)
    convert h using 1
    funext k
    simp only [smul_pow, map_smul, smul_eq_mul, AbelTraceMeans.coef]
    ring
  let p : Polynomial ℂ := ∑ i ∈ range (n + 1), Polynomial.C (τ (S ^ i * P)) * Polynomial.X ^ i
  have evalp (y : ℂ) : p.eval y = ∑ i ∈ range (n + 1), τ (S ^ i * P) * y ^ i := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have laurentBound (s : ℝ) (hs : 1 < s) (close : s - 1 < ρ) :
      ‖(γ * s - γ) * τ (resolvent B (γ * s)) - p.eval ((γ * s - γ)⁻¹)‖ ≤ (s - 1) * C := by
    have normSub := (norm_ray γ unit s hs).2
    have ne : (γ * s - γ : ℂ) ≠ 0 := by
      intro h; rw [h, norm_zero] at normSub; linarith
    have neγ : (γ * s : ℂ) ≠ γ := sub_ne_zero.mp ne
    have bound := lau (γ * s) (resolventMem s hs) (by rw [normSub]; exact close) neγ
    set y := (γ * s - γ : ℂ)⁻¹ with hy
    set L := ∑ j ∈ range (n + 1), y ^ (j + 1) • (S ^ j * P) with hL
    have polynomial : (γ * s - γ) * τ L = p.eval y := by
      rw [evalp, hL, map_sum, Finset.mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, pow_succ', ← mul_assoc, ← mul_assoc, hy,
        mul_inv_cancel₀ ne, one_mul, mul_comm]
    have difference : (γ * s - γ) * τ (resolvent B (γ * s)) - p.eval y =
        (γ * s - γ) * τ (resolvent B (γ * s) - L) := by
      rw [← polynomial, map_sub, mul_sub]
    rw [difference, norm_mul, normSub]
    have hτR : ‖τ (resolvent B (γ * s) - L)‖ ≤ ‖τ‖ * M :=
      (τ.le_opNorm _).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))
    have hM : ‖τ‖ * M ≤ C := by
      rw [hC]
      nlinarith [le_abs_self M, norm_nonneg τ]
    exact mul_le_mul_of_nonneg_left (hτR.trans hM) (by linarith)
  have abel := AbelTraceMeans.abel_compare γ unit (fun k => τ (B ^ k)) t (δ j) (compare j)
    periodic
  have degree : p.degree ≤ 0 := by
    by_contra positive
    push Not at positive
    have toInf : Tendsto (fun s : ℝ => ‖(γ * s - γ : ℂ)⁻¹‖) (𝓝[>] 1) atTop := by
      have shift : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have h : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
          rw [sub_self] at h
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact sub_pos.mpr hs
      refine (tendsto_inv_nhdsGT_zero.comp shift).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Function.comp_apply, norm_inv, (norm_ray γ unit s hs).2]
    have grow := Polynomial.tendsto_norm_atTop p positive toInf
    have bounded : ∀ᶠ s : ℝ in 𝓝[>] 1,
        ‖p.eval ((γ * (s : ℂ) - γ)⁻¹)‖ ≤ ‖e‖ + δ j + 1 + 1 := by
      filter_upwards [abel 1 one_pos, eventually_close (min ρ (1 / C)) (by positivity)]
        with s hA hclose
      have hs := hclose.1
      have near := laurentBound s hs (hclose.2.trans_le (min_le_left _ _))
      have hx := hA _ (series s hs)
      have prod : (s - 1) * C ≤ 1 := by
        have := hclose.2.trans_le (min_le_right _ _)
        rw [lt_div_iff₀ C0] at this
        linarith
      calc ‖p.eval ((γ * s - γ)⁻¹)‖
          ≤ ‖(γ * s - γ) * τ (resolvent B (γ * s))‖ +
            ‖(γ * s - γ) * τ (resolvent B (γ * s)) - p.eval ((γ * s - γ)⁻¹)‖ := by
            have := norm_sub_norm_le ((γ * s - γ) * τ (resolvent B (γ * s)))
              (p.eval ((γ * s - γ)⁻¹))
            have := norm_sub_rev ((γ * s - γ) * τ (resolvent B (γ * s)))
              (p.eval ((γ * s - γ)⁻¹))
            have := norm_le_insert' (p.eval ((γ * s - γ)⁻¹))
              ((γ * s - γ) * τ (resolvent B (γ * s)))
            linarith
        _ ≤ (‖e‖ + (δ j + 1)) + 1 := by
            refine add_le_add ?_ (near.trans prod)
            have := norm_le_insert' ((γ * s - γ) * τ (resolvent B (γ * s))) e
            linarith
        _ = ‖e‖ + δ j + 1 + 1 := by ring
    obtain ⟨s, big, le⟩ :=
      ((grow.eventually_gt_atTop (‖e‖ + δ j + 1 + 1)).and bounded).exists
    linarith
  have constant (y : ℂ) : p.eval y = τ P := by
    rw [Polynomial.eq_C_of_degree_le_zero degree, Polynomial.eval_C,
      Polynomial.coeff_zero_eq_eval_zero, evalp, Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      sum_const_zero, pow_zero, one_mul, mul_one, zero_add]
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨s, hA, hclose⟩ := ((abel (η / 2) (by positivity)).and
    (eventually_close (min ρ (η / 2 / C)) (by positivity))).exists
  have hs := hclose.1
  have near := laurentBound s hs (hclose.2.trans_le (min_le_left _ _))
  have hx := hA _ (series s hs)
  have prod : (s - 1) * C ≤ η / 2 := by
    have := hclose.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ C0] at this
    linarith
  rw [constant] at near
  calc ‖τ P - e‖ ≤ ‖(γ * s - γ) * τ (resolvent B (γ * s)) - e‖ +
        ‖(γ * s - γ) * τ (resolvent B (γ * s)) - τ P‖ := by
        have h1 := norm_sub_le_norm_sub_add_norm_sub (τ P)
          ((γ * s - γ) * τ (resolvent B (γ * s))) e
        have h2 := norm_sub_rev (τ P) ((γ * s - γ) * τ (resolvent B (γ * s)))
        linarith
    _ ≤ (δ j + η / 2) + η / 2 := add_le_add hx (near.trans prod)
    _ = δ j + η := by ring

theorem rank_eq (B : E →L[ℂ] E) (radius : spectralRadius ℂ B ≤ 1) (γ : ℂ) (unit : ‖γ‖ = 1)
    (n : ℕ) (compl : IsTopCompl ((B - γ • 1) ^ n).ker ((B - γ • 1) ^ n).range)
    (hker : ((B - γ • 1) ^ (n + 1)).ker = ((B - γ • 1) ^ n).ker)
    (hrange : ((B - γ • 1) ^ (n + 1)).range = ((B - γ • 1) ^ n).range)
    [FiniteDimensional ℂ ((B - γ • 1) ^ n).ker]
    {ι : Type*} {l : Filter ι} [l.NeBot] (F : ι → RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v ∈ ((B - γ • 1) ^ n).ker, ∀ φ : E →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) l (𝓝 (φ v)))
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop, ‖(F j).traceL (B ^ k) - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    Module.finrank ℂ ((B - γ • 1) ^ n).ker = if γ = 1 then 1 else 0 := by
  set S := B - γ • (1 : E →L[ℂ] E) with hS
  set P := (S ^ n).ker.projectionL (S ^ n).range compl with hP
  set e : ℂ := if γ = 1 then 1 else 0 with he
  have key := trace_close B radius γ unit n compl hker hrange F t periodic δ compare
  have rangeP : P.range = (S ^ n).ker := Submodule.range_projectionL compl
  have idem : P.comp P = P := (Submodule.isIdempotentElem_projectionL compl).eq
  have : FiniteDimensional ℂ P.range := by rw [rangeP]; infer_instance
  have lim1 := RegularizedTraceFunctional.projector_tendsto F P idem
    (fun v hv φ => weak v (rangeP ▸ hv) φ)
  have lim2 : Tendsto (fun j => (F j).traceL P) l (𝓝 e) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) key small)
  have same := tendsto_nhds_unique lim1 lim2
  have finrankEq : Module.finrank ℂ P.range = Module.finrank ℂ (S ^ n).ker := by rw [rangeP]
  rw [finrankEq] at same
  by_cases one : γ = 1
  · simp only [he, one, ↓reduceIte] at same ⊢
    exact_mod_cast same
  · simp only [he, one, ↓reduceIte] at same ⊢
    exact_mod_cast same

/-- If the smoothings converge weakly to `B v` on the generalized kernel, the regularized
traces of the Fitting projection converge to the trace `γ · dim` of `B` on that kernel. -/
theorem kernel_trace_tendsto (B : E →L[ℂ] E) (γ : ℂ)
    (n : ℕ) (compl : IsTopCompl ((B - γ • 1) ^ n).ker ((B - γ • 1) ^ n).range)
    [FiniteDimensional ℂ ((B - γ • 1) ^ n).ker]
    {ι : Type*} {l : Filter ι} (F : ι → RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v ∈ ((B - γ • 1) ^ n).ker, ∀ φ : E →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) l (𝓝 (φ (B v)))) :
    Tendsto (fun j => (F j).traceL
      (((B - γ • 1) ^ n).ker.projectionL ((B - γ • 1) ^ n).range compl)) l
      (𝓝 (γ * Module.finrank ℂ ((B - γ • 1) ^ n).ker)) := by
  set S := B - γ • (1 : E →L[ℂ] E) with hS
  set K := (S ^ n).ker with hK
  set V := (S ^ n).range
  set P := K.projectionL V compl with hP
  let basis := Module.finBasis ℂ K
  let proj : E →L[ℂ] K := K.projectionOntoL V compl
  let c : Fin (Module.finrank ℂ K) → E →L[ℂ] ℂ :=
    fun i => (LinearMap.toContinuousLinearMap (basis.coord i)).comp proj
  have expansion : P = ∑ i, (c i).smulRight (basis i : E) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := basis.sum_repr (proj x)
    rw [show (∑ i, (c i).smulRight (basis i : E)) x = ∑ i, ((c i).smulRight (basis i : E)) x from
      map_sum (ContinuousLinearMap.apply ℂ E x) _ _]
    simp only [ContinuousLinearMap.smulRight_apply]
    have coe := congrArg (fun v : K => (v : E)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at coe
    exact coe.symm
  have each (j : ι) : (F j).traceL P = ∑ i, c i ((F j).smoothing (basis i)) := by
    conv_lhs => rw [expansion]
    rw [map_sum]
    exact sum_congr rfl fun i _ => (F j).traceL_smulRight (c i) (basis i)
  have limit : Tendsto (fun j => ∑ i, c i ((F j).smoothing (basis i))) l
      (𝓝 (∑ i, c i (B (basis i)))) :=
    tendsto_finsetSum _ fun i _ => weak _ (basis i).property (c i)
  have invariant (k : K) : B k ∈ K := by
    have Sk : S k ∈ K := by
      change (S ^ n) (S k) = 0
      rw [← mul_apply_eq_comp, ← pow_succ, pow_succ', mul_apply_eq_comp,
        show (S ^ n) (k : E) = 0 from k.property, map_zero]
    have : B k = S k + γ • (k : E) := by
      rw [hS, sub_apply, smul_apply,
        one_apply_eq_self, sub_add_cancel]
    rw [this]
    exact K.add_mem Sk (K.smul_mem γ k.property)
  let Bk : K →L[ℂ] K := proj ∘L (B ∘L K.subtypeL)
  have Bk_apply (k : K) : (Bk k : E) = B k := by
    change ((K.projectionOntoL V compl (B k) : K) : E) = B k
    rw [show B k = ((⟨B k, invariant k⟩ : K) : E) from rfl,
      Submodule.projectionOntoL_apply_left]
  have shiftApply (k : K) :
      (((Bk.toLinearMap - algebraMap ℂ (Module.End ℂ K) γ) k : K) : E) = S k := by
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub,
      Submodule.coe_smul, ContinuousLinearMap.coe_coe, Bk_apply, hS,
      sub_apply, smul_apply,
      one_apply_eq_self]
  have powers (m : ℕ) (k : K) :
      ((((Bk.toLinearMap - algebraMap ℂ (Module.End ℂ K) γ) ^ m) k : K) : E) = (S ^ m) k := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, shiftApply, ih, ← mul_apply_eq_comp,
        ← pow_succ']
  have nilpotent : IsNilpotent (Bk.toLinearMap - algebraMap ℂ (Module.End ℂ K) γ) := by
    refine ⟨n, LinearMap.ext fun k => Subtype.ext ?_⟩
    rw [powers]
    exact k.property
  have traceBk := StrongFiniteSpectralTrace.trace_powers_of_shift_nilpotent
    Bk.toLinearMap γ nilpotent 1
  rw [pow_one, pow_one, StrongFiniteSpectralTrace.trace_eq_coordinates] at traceBk
  have value : ∑ i, c i (B (basis i)) = γ * Module.finrank ℂ K := by
    rw [mul_comm, ← traceBk]
    rfl
  rw [value] at limit
  exact limit.congr fun j => (each j).symm

/-- Peripheral ranks when the smoothings tend weakly to `B v` (smoothings that end with
an application of `B`). -/
theorem rank_eq_shift (B : E →L[ℂ] E) (radius : spectralRadius ℂ B ≤ 1) (γ : ℂ)
    (unit : ‖γ‖ = 1)
    (n : ℕ) (compl : IsTopCompl ((B - γ • 1) ^ n).ker ((B - γ • 1) ^ n).range)
    (hker : ((B - γ • 1) ^ (n + 1)).ker = ((B - γ • 1) ^ n).ker)
    (hrange : ((B - γ • 1) ^ (n + 1)).range = ((B - γ • 1) ^ n).range)
    [FiniteDimensional ℂ ((B - γ • 1) ^ n).ker]
    {ι : Type*} {l : Filter ι} [l.NeBot] (F : ι → RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v ∈ ((B - γ • 1) ^ n).ker, ∀ φ : E →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) l (𝓝 (φ (B v))))
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop, ‖(F j).traceL (B ^ k) - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    Module.finrank ℂ ((B - γ • 1) ^ n).ker = if γ = 1 then 1 else 0 := by
  have key := trace_close B radius γ unit n compl hker hrange F t periodic δ compare
  have lim1 := kernel_trace_tendsto B γ n compl F weak
  have lim2 : Tendsto (fun j => (F j).traceL
      (((B - γ • 1) ^ n).ker.projectionL ((B - γ • 1) ^ n).range compl)) l
      (𝓝 (if γ = 1 then 1 else 0)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) key small)
  have same := tendsto_nhds_unique lim1 lim2
  have γ0 : γ ≠ 0 := by intro h; rw [h, norm_zero] at unit; exact zero_ne_one unit
  by_cases one : γ = 1
  · simp only [one, ↓reduceIte, one_mul] at same ⊢
    exact_mod_cast same
  · simp only [one, ↓reduceIte] at same ⊢
    have : (Module.finrank ℂ ((B - γ • 1) ^ n).ker : ℂ) = 0 :=
      (mul_eq_zero.mp same).resolve_left γ0
    exact_mod_cast this

end LeanShared.AbelTraceRank
