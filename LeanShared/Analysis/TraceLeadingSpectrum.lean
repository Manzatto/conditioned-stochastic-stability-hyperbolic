module
public import LeanShared.Analysis.AbelTraceRank
public import LeanShared.Analysis.CompactTwoNormDecomposition
public import LeanShared.Analysis.CompactTwoNormDiscreteSpectrum
public import LeanShared.Analysis.FittingContour
public import LeanShared.Analysis.ShiftedContour
public import LeanShared.Analysis.RieszComplementSpectrum
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! A separated simple leading eigenvalue from regularized traces. Let `T` satisfy a
compact two-norm estimate with strong rate `α < λ`, spectral radius at most `λ`, and
`λ ∈ σ(T)`. If for some `N > 0` the regularized traces of the powers of
`B = λ^{-N} T^N` stay within `δ_j → 0` of a sequence tending to one, and the smoothings
converge weakly to `B v`, then `λ` is the only spectral value of modulus `λ`, it is a
simple eigenvalue with a rank-one invariant projection `h ⊗ m`, and the rest of the
spectrum lies in a disk of radius `q < λ`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Filter Finset Set Metric ContinuousLinearMap Submodule
open scoped Topology NNReal ENNReal
namespace LeanShared.TraceLeadingSpectrum

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- An outer spectral value of a compact two-norm operator has an eigenvector. -/
theorem eigenvector_of_mem (T : E →L[ℂ] E) (i : E →L[ℂ] W) (hi : IsCompactOperator i)
    (α R C D : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (z : ℂ) (hz : α < ‖z‖) (mem : z ∈ spectrum ℂ T) : ∃ h : E, h ≠ 0 ∧ T h = z • h := by
  by_contra none
  push Not at none
  obtain ⟨n, _, compl, _, ranges⟩ :=
    CompactTwoNormDecomposition.exists_decomposition T i hi α R C D hα hR hC hD estimate z hz
  set S := T - z • (1 : E →L[ℂ] E) with hS
  have injS (x : E) (hx : S x = 0) : x = 0 := by
    by_contra hne
    refine none x hne ?_
    rw [hS, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at hx
    exact hx
  have kerPow (m : ℕ) (x : E) (hx : (S ^ m) x = 0) : x = 0 := by
    induction m generalizing x with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ, mul_apply_eq_comp] at hx
      exact injS x (ih _ hx)
  have Vtop : (S ^ n).range = ⊤ := by
    have kerBot : (S ^ n).ker = ⊥ := (Submodule.eq_bot_iff _).mpr fun x hx => kerPow n x hx
    have complement := compl.isCompl
    rw [kerBot] at complement
    exact eq_top_of_bot_isCompl complement
  have surj : Function.Surjective S := by
    intro y
    have : y ∈ (S ^ (n + 1)).range := by rw [ranges 1, Vtop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨(S ^ n) x, by rw [← hx, pow_succ']; rfl⟩
  have bij : Function.Bijective S :=
    ⟨fun x y hxy => sub_eq_zero.mp (injS _ (by rw [map_sub, hxy, sub_self])), surj⟩
  have unit : IsUnit S := ContinuousLinearMap.isUnit_iff_bijective.mpr bij
  have shift : algebraMap ℂ (E →L[ℂ] E) z - T = -S := by
    rw [hS, Algebra.algebraMap_eq_smul_one]; abel
  exact spectrum.mem_iff.mp mem (by rw [shift]; exact unit.neg)

/-- Powers act on eigenvectors by powers of the eigenvalue. -/
theorem pow_eigen (T : E →L[ℂ] E) (z : ℂ) (h : E) (eigen : T h = z • h) (k : ℕ) :
    (T ^ k) h = z ^ k • h := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, eigen, smul_smul, pow_succ]

theorem scaled_estimate (T : E →L[ℂ] E) (i : E →L[ℂ] W) (α R C D : ℝ)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (lam : ℝ) (lam_pos : 0 < lam) (N : ℕ) (k : ℕ) (x : E) :
    ‖((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k) x‖ ≤
      C * ((α / lam) ^ N) ^ k * ‖x‖ + D * ((R / lam) ^ N) ^ k * ‖i x‖ := by
  rw [smul_pow, ← pow_mul, smul_apply, norm_smul]
  have scalar : ‖(((lam : ℂ) ^ N)⁻¹) ^ k‖ = (lam⁻¹) ^ (N * k) := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg lam_pos.le,
      ← inv_pow, ← pow_mul]
  rw [scalar]
  have base := estimate (N * k) x
  have positive : 0 ≤ (lam⁻¹) ^ (N * k) := by positivity
  calc (lam⁻¹) ^ (N * k) * ‖(T ^ (N * k)) x‖
      ≤ (lam⁻¹) ^ (N * k) * (C * α ^ (N * k) * ‖x‖ + D * R ^ (N * k) * ‖i x‖) :=
        mul_le_mul_of_nonneg_left base positive
    _ = C * ((α / lam) ^ N) ^ k * ‖x‖ + D * ((R / lam) ^ N) ^ k * ‖i x‖ := by
        rw [← pow_mul, ← pow_mul, div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow]
        ring

theorem norm_le_of_radius (T : E →L[ℂ] E) (lam : ℝ) (hlam : 0 ≤ lam)
    (radius : spectralRadius ℂ T ≤ ENNReal.ofReal lam) (w : ℂ) (hw : w ∈ spectrum ℂ T) :
    ‖w‖ ≤ lam := by
  rw [spectralRadius_eq_of_unital] at radius
  have := (le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ T) => (‖k‖₊ : ℝ≥0∞)) w hw).trans radius
  exact (ENNReal.ofReal_le_ofReal_iff hlam).mp (by rw [ofReal_norm]; exact this)

theorem scaled_radius (T : E →L[ℂ] E) (lam : ℝ) (lam_pos : 0 < lam)
    (radius : spectralRadius ℂ T ≤ ENNReal.ofReal lam) (N : ℕ) (hN : 0 < N) :
    spectralRadius ℂ (((lam : ℂ) ^ N)⁻¹ • T ^ N) ≤ 1 := by
  refine iSup₂_le fun z hzq => ?_
  rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff] at hzq
  rcases hzq with hz | zero
  swap
  · rw [zero, nnnorm_zero, ENNReal.coe_zero]; exact zero_le_one
  have c0 : ((lam : ℂ) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast lam_pos.ne'))
  have unitForm : ((lam : ℂ) ^ N)⁻¹ • T ^ N = (Units.mk0 _ c0) • T ^ N := by
    rw [Units.smul_def, Units.val_mk0]
  rw [unitForm, spectrum.unit_smul_eq_smul] at hz
  obtain ⟨v, hv, hvz⟩ := Set.mem_smul_set.mp hz
  rw [spectrum.map_pow_of_pos (𝕜 := ℂ) T hN] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have hwz : z = ((lam : ℂ) ^ N)⁻¹ * w ^ N := by
    rw [← hvz, ← hwv, Units.smul_def, Units.val_mk0, smul_eq_mul]
  have wle : ‖w‖ ≤ lam := norm_le_of_radius T lam lam_pos.le radius w hw
  have zeq : z = ((lam : ℂ) ^ N)⁻¹ * w ^ N := hwz
  have znorm : ‖z‖ ≤ 1 := by
    rw [zeq, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg lam_pos.le]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) wle N
  have : (‖z‖₊ : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]; exact znorm
  exact_mod_cast this

/-- Generalized kernels of `T - λ` lie in those of `λ^{-N} T^N - 1`. -/
theorem kernel_le (T : E →L[ℂ] E) (lam : ℂ) (lam0 : lam ≠ 0) (N m : ℕ) (x : E)
    (hx : ((T - lam • 1) ^ m) x = 0) : (((lam ^ N)⁻¹ • T ^ N - 1) ^ m) x = 0 := by
  set G : E →L[ℂ] E := (lam ^ N)⁻¹ • ∑ i ∈ range N, T ^ i * (lam • (1 : E →L[ℂ] E)) ^ (N - 1 - i)
  have commuteT : Commute T (lam • (1 : E →L[ℂ] E)) := (Commute.one_right T).smul_right lam
  have factor : (lam ^ N)⁻¹ • T ^ N - 1 = G * (T - lam • 1) := by
    rw [smul_mul_assoc, commuteT.geom_sum₂_mul N, smul_sub, smul_pow, one_pow, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero N lam0), one_smul]
  have comm : Commute G (T - lam • 1) := by
    refine Commute.smul_left ?_ _
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact Commute.mul_left ((Commute.sub_right (Commute.refl T) commuteT).pow_left i)
      ((Commute.smul_left (Commute.one_left _) lam).pow_left _)
  rw [factor, comm.mul_pow, mul_apply_eq_comp, hx, map_zero]

/-- The separated simple leading eigenvalue from regularized traces. -/
theorem leading (T : E →L[ℂ] E) (i : E →L[ℂ] W) (hi : IsCompactOperator i)
    (α R C D : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (lam : ℝ) (lam_pos : 0 < lam) (gap : α < lam)
    (radius : spectralRadius ℂ T ≤ ENNReal.ofReal lam)
    (positive : (lam : ℂ) ∈ spectrum ℂ T) (N : ℕ) (hN : 0 < N)
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y]
    {ι : Type*} {l : Filter ι} [l.NeBot] (F : ι → RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v : E, ∀ φ : E →L[ℂ] ℂ, Tendsto (fun j => φ ((F j).smoothing v)) l
      (𝓝 (φ ((((lam : ℂ) ^ N)⁻¹ • T ^ N) v))))
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop,
      ‖(F j).traceL ((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k) - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    ∃ (h : E) (m : E →L[ℂ] ℂ) (q : ℝ), 0 ≤ q ∧ q < lam ∧ m h = 1 ∧ T h = (lam : ℂ) • h ∧
      (∀ x, m (T x) = (lam : ℂ) * m x) ∧
      spectralRadius ℂ (T - m.smulRight ((lam : ℂ) • h)) ≤ ENNReal.ofReal q ∧
      (∀ z ∈ spectrum ℂ T, z = lam ∨ ‖z‖ ≤ q) ∧
      (∀ x, T x = (lam : ℂ) • x → ∃ c : ℂ, x = c • h) := by
  set B := ((lam : ℂ) ^ N)⁻¹ • T ^ N with hB
  have lamC : (lam : ℂ) ≠ 0 := by exact_mod_cast lam_pos.ne'
  have normLam : ‖(lam : ℂ)‖ = lam := by
    rw [Complex.norm_real, Real.norm_of_nonneg lam_pos.le]
  have ratio : (α / lam) ^ N < 1 :=
    pow_lt_one₀ (div_nonneg hα lam_pos.le) ((div_lt_one lam_pos).mpr gap) hN.ne'
  have estimateB := scaled_estimate T i α R C D estimate lam lam_pos N
  have radiusB := scaled_radius T lam lam_pos radius N hN
  have fitting (γ : ℂ) (unit : ‖γ‖ = 1) : ∃ n : ℕ, FiniteDimensional ℂ ((B - γ • 1) ^ n).ker ∧
      (∀ k, ((B - γ • 1) ^ (n + k)).ker = ((B - γ • 1) ^ n).ker) ∧
      Module.finrank ℂ ((B - γ • 1) ^ n).ker = if γ = 1 then 1 else 0 := by
    obtain ⟨n, finite, compl, kernels, ranges⟩ :=
      CompactTwoNormDecomposition.exists_decomposition B i hi ((α / lam) ^ N) ((R / lam) ^ N)
        C D (pow_nonneg (div_nonneg hα lam_pos.le) N) (pow_nonneg (div_nonneg hR lam_pos.le) N)
        hC hD estimateB γ (by rw [unit]; exact ratio)
    exact ⟨n, finite, kernels, AbelTraceRank.rank_eq_shift B radiusB γ unit n compl (kernels 1)
      (ranges 1) F (fun v _ φ => weak v φ) t periodic δ compare small⟩
  have inKernel (γ : ℂ) (n : ℕ)
      (kernels : ∀ k, ((B - γ • 1) ^ (n + k)).ker = ((B - γ • 1) ^ n).ker)
      (v : E) (hv : B v = γ • v) : v ∈ ((B - γ • 1) ^ n).ker := by
    rw [← kernels 1]
    change ((B - γ • 1) ^ (n + 1)) v = 0
    have zero : (B - γ • 1) v = 0 := by
      have expand : (B - γ • 1) v = B v - γ • v := rfl
      rw [expand, hv, sub_self]
    rw [pow_succ, mul_apply_eq_comp, zero, map_zero]
  obtain ⟨h0, h0ne, h0eig⟩ := eigenvector_of_mem T i hi α R C D hα hR hC hD estimate lam
    (by rw [normLam]; exact gap) positive
  have fixed (x : E) (hx : T x = (lam : ℂ) • x) : B x = (1 : ℂ) • x := by
    rw [hB, smul_apply, pow_eigen T _ x hx N, smul_smul, inv_mul_cancel₀ (pow_ne_zero N lamC)]
  obtain ⟨n1, _, kernels1, rank1⟩ := fitting 1 norm_one
  simp only [↓reduceIte] at rank1
  have h0mem := inKernel 1 n1 kernels1 h0 (fixed h0 h0eig)
  have spanned (v : E) (hv : v ∈ ((B - (1 : ℂ) • 1) ^ n1).ker) : ∃ c : ℂ, v = c • h0 := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨h0, h0mem⟩ : ((B - (1 : ℂ) • 1) ^ n1).ker)
      (fun h => h0ne (congrArg Subtype.val h))).mp rank1 ⟨v, hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have unitEigen (w : ℂ) (unit : ‖w‖ = 1) (v : E) (hv : B v = w • v) (vne : v ≠ 0) : w = 1 := by
    by_contra wne
    obtain ⟨n, _, kernels, rank⟩ := fitting w unit
    simp only [wne, ↓reduceIte] at rank
    have mem := inKernel w n kernels v hv
    rw [Submodule.finrank_eq_zero.mp rank] at mem
    exact vne ((Submodule.mem_bot ℂ).mp mem)
  have peripheral (z : ℂ) (hz : z ∈ spectrum ℂ T) (hnorm : ‖z‖ = lam) : z = lam := by
    obtain ⟨v, vne, veig⟩ := eigenvector_of_mem T i hi α R C D hα hR hC hD estimate z
      (by rw [hnorm]; exact gap) hz
    have Bv : B v = (((lam : ℂ) ^ N)⁻¹ * z ^ N) • v := by
      rw [hB, smul_apply, pow_eigen T z v veig N, smul_smul]
    have wunit : ‖((lam : ℂ) ^ N)⁻¹ * z ^ N‖ = 1 := by
      rw [norm_mul, norm_inv, norm_pow, norm_pow, normLam, hnorm,
        inv_mul_cancel₀ (pow_ne_zero _ lam_pos.ne')]
    have w1 := unitEigen _ wunit v Bv vne
    obtain ⟨c, hc⟩ := spanned v (inKernel 1 n1 kernels1 v (by rw [Bv, w1]))
    have Tlam : T v = (lam : ℂ) • v := by rw [hc, map_smul, h0eig, smul_comm]
    have zero : (z - lam) • v = 0 := by rw [sub_smul, ← veig, Tlam, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp zero).resolve_right vne)
  have simple (x : E) (hx : T x = (lam : ℂ) • x) : ∃ c : ℂ, x = c • h0 :=
    spanned x (inKernel 1 n1 kernels1 x (fixed x hx))
  obtain ⟨nT, _, complT, kernelsT, rangesT⟩ :=
    CompactTwoNormDecomposition.exists_decomposition T i hi α R C D hα hR hC hD estimate
      (lam : ℂ) (by rw [normLam]; exact gap)
  set S := T - (lam : ℂ) • (1 : E →L[ℂ] E) with hS
  set P := (S ^ nT).ker.projectionL (S ^ nT).range complT with hP
  have KTspan (x : E) (hx : x ∈ (S ^ nT).ker) : ∃ c : ℂ, x = c • h0 := by
    have hB1 := kernel_le T lam lamC N nT x hx
    apply spanned
    rw [← kernels1 nT]
    change ((B - (1 : ℂ) • 1) ^ (n1 + nT)) x = 0
    rw [one_smul, pow_add, mul_apply_eq_comp, hB1, map_zero]
  have h0K : h0 ∈ (S ^ nT).ker := by
    rw [← kernelsT 1]
    change (S ^ (nT + 1)) h0 = 0
    have zero : S h0 = 0 := by rw [hS, sub_apply, smul_apply, one_apply_eq_self, h0eig, sub_self]
    rw [pow_succ, mul_apply_eq_comp, zero, map_zero]
  have Ph0 : P h0 = h0 := Submodule.projectionL_apply_left complT ⟨h0, h0K⟩
  have commTS : Commute T (S ^ nT) :=
    (Commute.sub_right (Commute.refl T) ((Commute.one_right T).smul_right _)).pow_right nT
  have PT (x : E) : P (T x) = T (P x) := by
    have kmem : P x ∈ (S ^ nT).ker := Submodule.projectionL_apply_mem complT x
    have vmem : (S ^ nT).range.projectionL (S ^ nT).ker complT.symm x ∈ (S ^ nT).range :=
      Submodule.projectionL_apply_mem complT.symm x
    have decomposition := (Submodule.projectionL_add_projectionL_eq_self complT x).symm
    have Tk : T (P x) ∈ (S ^ nT).ker := by
      change (S ^ nT) (T (P x)) = 0
      rw [← mul_apply_eq_comp, ← commTS.eq, mul_apply_eq_comp,
        show (S ^ nT) (P x) = 0 from kmem, map_zero]
    have Tv : T ((S ^ nT).range.projectionL (S ^ nT).ker complT.symm x) ∈ (S ^ nT).range := by
      obtain ⟨y, hy⟩ := vmem
      refine ⟨T y, ?_⟩
      rw [← hy]
      change (S ^ nT) (T y) = T ((S ^ nT) y)
      rw [← mul_apply_eq_comp, ← commTS.eq, mul_apply_eq_comp]
    conv_lhs => rw [decomposition]
    rw [map_add, map_add, Submodule.projectionL_apply_left complT ⟨_, Tk⟩,
      Submodule.projectionL_apply_right complT ⟨_, Tv⟩, add_zero]
  have TP (x : E) : T (P x) = (lam : ℂ) • P x := by
    obtain ⟨c, hc⟩ := KTspan (P x) (Submodule.projectionL_apply_mem complT x)
    rw [hc, map_smul, h0eig, smul_comm]
  obtain ⟨φ, -, φh0⟩ := exists_dual_vector ℂ h0 (norm_ne_zero_iff.mpr h0ne)
  have φne : φ h0 ≠ 0 := by
    rw [φh0]; exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0ne)
  set m : E →L[ℂ] ℂ := (φ h0)⁻¹ • (φ.comp P) with hm
  have Pform (x : E) : P x = m x • h0 := by
    obtain ⟨c, hc⟩ := KTspan (P x) (Submodule.projectionL_apply_mem complT x)
    have value : m x = c := by
      rw [hm, smul_apply, comp_apply, hc, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        mul_comm _ c, mul_assoc, inv_mul_cancel₀ φne, mul_one]
    rw [value, hc]
  have mh0 : m h0 = 1 := by
    rw [hm, smul_apply, comp_apply, Ph0, smul_eq_mul, inv_mul_cancel₀ φne]
  have mT (x : E) : m (T x) = (lam : ℂ) * m x := by
    rw [hm, smul_apply, smul_apply, comp_apply, comp_apply, PT, TP, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring
  set q0 := (α + lam) / 2 with hq0
  have q0gt : α < q0 := by rw [hq0]; linarith
  have q0lt : q0 < lam := by rw [hq0]; linarith
  have finiteOuter := CompactTwoNormDiscreteSpectrum.finite_outer_spectrum T i hi α R C D
    hα hR hC hD estimate q0 q0gt
  set s' := finiteOuter.toFinset.filter (fun z => z ≠ (lam : ℂ)) with hs'
  set qmax : ℝ≥0 := s'.sup (fun z => ‖z‖₊) with hqmax
  have qmaxlt : (qmax : ℝ) < lam := by
    have lt : qmax < lam.toNNReal := by
      rw [hqmax, Finset.sup_lt_iff (by simpa using lam_pos)]
      intro z hz
      rw [hs', Finset.mem_filter, Set.Finite.mem_toFinset] at hz
      obtain ⟨⟨zσ, _⟩, zne⟩ := hz
      have le := norm_le_of_radius T lam lam_pos.le radius z zσ
      have strict : ‖z‖ < lam := lt_of_le_of_ne le (fun e => zne (peripheral z zσ e))
      rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.coe_toNNReal _ lam_pos.le]
      exact strict
    have := NNReal.coe_lt_coe.mpr lt
    rwa [Real.coe_toNNReal _ lam_pos.le] at this
  set q := max q0 (qmax : ℝ) with hq
  have q_nonneg : 0 ≤ q := le_max_of_le_left (by rw [hq0]; linarith)
  have q_lt : q < lam := max_lt q0lt qmaxlt
  have separation (z : ℂ) (hz : z ∈ spectrum ℂ T) : z = lam ∨ ‖z‖ ≤ q := by
    by_cases zl : z = lam
    · exact Or.inl zl
    right
    by_cases below : ‖z‖ < q0
    · exact below.le.trans (le_max_left _ _)
    have mem : z ∈ s' := by
      rw [hs', Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hz, not_lt.mp below⟩, zl⟩
    have bound := Finset.le_sup (f := fun z => ‖z‖₊) mem
    have real : ‖z‖ ≤ (qmax : ℝ) := by
      rw [← coe_nnnorm]; exact_mod_cast bound
    exact real.trans (le_max_right _ _)
  obtain ⟨r, hr, contours⟩ := FittingContour.exists_contours S nT complT (kernelsT 1) (rangesT 1)
  have ρpos : 0 < r / 2 := half_pos hr
  obtain ⟨resS, projS⟩ := contours (r / 2) ρpos (half_lt_self hr)
  have projT : RieszContourIdempotent.projector T (lam : ℂ) (r / 2) = P := by
    rw [← ShiftedContour.formula T (lam : ℂ) (r / 2)]; exact projS
  have resT : sphere (lam : ℂ) (r / 2) ⊆ resolventSet ℂ T := by
    intro w hw
    have hs := resS (show w - lam ∈ sphere (0 : ℂ) (r / 2) by
      simpa only [mem_sphere, dist_eq_norm, sub_zero] using hw)
    change IsUnit (algebraMap ℂ (E →L[ℂ] E) (w - lam) - S) at hs
    have shift : algebraMap ℂ (E →L[ℂ] E) (w - lam) - S = algebraMap ℂ (E →L[ℂ] E) w - T := by
      rw [hS]
      simp only [Algebra.algebraMap_eq_smul_one, sub_smul]
      abel
    rw [shift] at hs
    exact hs
  have idem : P * P = P := (Submodule.isIdempotentElem_projectionL complT).eq
  have right : T * P = (lam : ℂ) • P := ContinuousLinearMap.ext fun x => TP x
  have left : P * T = (lam : ℂ) • P := ContinuousLinearMap.ext fun x => by
    rw [mul_apply_eq_comp, PT, TP]; rfl
  have smulRightEq : m.smulRight ((lam : ℂ) • h0) = (lam : ℂ) • P :=
    ContinuousLinearMap.ext fun x => by
      change m x • ((lam : ℂ) • h0) = (lam : ℂ) • P x
      rw [Pform, smul_comm]
  refine ⟨h0, m, q, q_nonneg, q_lt, mh0, h0eig, mT, ?_, separation, simple⟩
  rw [smulRightEq, spectralRadius_eq_of_unital]
  refine iSup₂_le fun z hz => ?_
  rw [← projT] at hz
  rcases RieszComplementSpectrum.inclusion T (lam : ℂ) (lam : ℂ) (r / 2) ρpos.le resT
      (mem_ball_self ρpos) (by rw [projT]; exact idem) (by rw [projT]; exact right)
      (by rw [projT]; exact left) z hz with zero | ⟨zσ, far⟩
  · rw [zero, nnnorm_zero, ENNReal.coe_zero]; exact bot_le
  · have zne : z ≠ lam := fun e => by rw [e, dist_self] at far; linarith
    have bound := (separation z zσ).resolve_left zne
    have h2 : ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal bound
    rw [ofReal_norm] at h2
    exact h2

end LeanShared.TraceLeadingSpectrum
