module

public import LeanShared.Geometry.ChartPairTransfer

/-!
# Finite-regular chart-pair realization and norm aggregation

The exact chart-pair function identity is lifted through faithful ordinary
finite-Hölder representations. Local anisotropic realization then gives an
identity of the actual chart vectors. The global maximum norm is bounded by
finite row sums of local microscopic bounds. No global finite-block bound
or completed chart decomposition is supplied.

Classical inputs are membership in the little finite-Hölder local ranges,
local anisotropic realization and the precise per-pair microscopic estimate.
These are independent of noise averaging and spectral conclusions.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanShared.RegularChartPairTransfer

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Linear zero-extended chart coordinate on arbitrary actual functions. -/
def coordinate (e : OpenPartialHomeomorph M E) (θ : M → ℂ) : (M → ℂ) →ₗ[ℂ] (E → ℂ) where
  toFun f := ChartLocalization.coordinate e θ f
  map_add' f h := by
    funext y
    by_cases hy : y ∈ e.target
    · simp only [ChartLocalization.coordinate, ite_eq_left hy, Pi.add_apply, mul_add]
    · simp only [Pi.add_apply, ChartLocalization.coordinate, ite_eq_right hy, zero_add]
  map_smul' c f := by
    funext y
    by_cases hy : y ∈ e.target
    · simp only [ChartLocalization.coordinate, ite_eq_left hy, Pi.smul_apply, smul_eq_mul]
      exact mul_left_comm _ _ _
    · simp only [Pi.smul_apply, ChartLocalization.coordinate, ite_eq_right hy, smul_zero]

omit [NormedSpace ℝ E] [ChartedSpace E M] in
@[simp] theorem coordinate_apply (e : OpenPartialHomeomorph M E) (θ : M → ℂ)
    (f : M → ℂ) (y : E) : coordinate e θ f y = ChartLocalization.coordinate e θ f y := rfl

/-- Faithful representation constructs a lift of the literal function map. -/
def lift {Input R : Type*} [AddCommGroup Input] [Module ℂ Input]
    [AddCommGroup R] [Module ℂ R] (view : R →ₗ[ℂ] (E → ℂ)) (inj : Function.Injective view)
    (L : Input →ₗ[ℂ] (E → ℂ)) (member : ∀ f, L f ∈ view.range) : Input →ₗ[ℂ] R :=
  (LinearEquiv.ofInjective view inj).symm.toLinearMap.comp (L.codRestrict view.range member)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lift_view {Input R : Type*} [AddCommGroup Input] [Module ℂ Input]
    [AddCommGroup R] [Module ℂ R] (view : R →ₗ[ℂ] (E → ℂ)) (inj : Function.Injective view)
    (L : Input →ₗ[ℂ] (E → ℂ)) (member : ∀ f, L f ∈ view.range) (f : Input) :
    view (lift view inj L member f) = L f :=
  LinearEquiv.ofInjective_symm_apply (f := view) (h := inj) ⟨L f, member f⟩

variable {AtlasIndex Core Reg : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (zero : ∀ f : Core, ∀ x ∉ S, functions f x = 0)
  (view : Reg →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
  (F : M → M) (g : M → ℝ)
  (regular : ∀ c, FiniteRegularTransferRealization.weightedComposition F g (functions c) ∈ view.range)
  {LocalReg : D.indices → Type*} [∀ i, AddCommGroup (LocalReg i)] [∀ i, Module ℂ (LocalReg i)]
  (localView : ∀ i, LocalReg i →ₗ[ℂ] (E → ℂ)) (localInj : ∀ i, Function.Injective (localView i))
  (coordinateMember : ∀ i f, coordinate (e i) (D.cutoff i) (view f) ∈ (localView i).range)
  (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
    ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g f.val ∈ (localView i).range)

def globalAction : Core →ₗ[ℂ] Reg :=
  FiniteRegularTransferRealization.regularAction functions Reg view inj (fun _ : Unit => F) g
    (fun _ => regular) ()

def localCoordinate (i : D.indices) : Reg →ₗ[ℂ] LocalReg i :=
  lift (localView i) (localInj i) ((coordinate (e i) (D.cutoff i)).comp view) (coordinateMember i)

def sourceFunction (j : D.indices) :
    SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j) →ₗ[ℂ] (E → ℂ) where
  toFun f := f.val
  map_add' f h := by funext y; rfl
  map_smul' c f := by funext y; rfl

def localPair (i j : D.indices) :
    SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j) →ₗ[ℂ] LocalReg i :=
  lift (localView i) (localInj i)
    ((ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g).comp
      (sourceFunction e D j))
    (pairMember i j)

include zero in
/-- Faithfulness lifts the literal partial chart identity to the actual
ordinary finite-regular ranges, before applying anisotropic realization. -/
theorem coordinate_action (i : D.indices) (c : Core) :
    localCoordinate e D view localView localInj coordinateMember i
      (globalAction functions view inj F g regular c) =
      ∑ j : D.indices, localPair e D F g localView localInj pairMember i j
        (ConstructedManifoldLocalization.localize e D he functions smooth j c) := by
  apply localInj i
  rw [map_sum]
  have hglobal := fun x => FiniteRegularTransferRealization.regularAction_apply
    functions Reg view inj (fun _ : Unit => F) g (fun _ => regular) () c x
  have hv : view (globalAction functions view inj F g regular c) =
      FiniteRegularTransferRealization.weightedComposition F g (functions c) := funext hglobal
  calc
    localView i (localCoordinate e D view localView localInj coordinateMember i
        (globalAction functions view inj F g regular c)) =
        coordinate (e i) (D.cutoff i) (view (globalAction functions view inj F g regular c)) :=
      lift_view (localView i) (localInj i) ((coordinate (e i) (D.cutoff i)).comp view)
        (coordinateMember i) _
    _ = ∑ j : D.indices, ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g
        (ConstructedManifoldLocalization.localize e D he functions smooth j c).val := by
      rw [hv]
      funext y
      simpa only [coordinate_apply, Finset.sum_apply] using
        ChartPairTransfer.coordinate_decomposition e D he functions smooth zero F g i c y
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (lift_view (localView i) (localInj i)
        ((ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g).comp (sourceFunction e D j))
        (pairMember i j) (ConstructedManifoldLocalization.localize e D he functions smooth j c)).symm

variable {B : D.indices → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  (realize : ∀ i, LocalReg i →ₗ[ℂ] B i)

include zero in
/-- The actual local realized output is the finite microlocal matrix row. -/
theorem realized_action (i : D.indices) (c : Core) :
    realize i (localCoordinate e D view localView localInj coordinateMember i
      (globalAction functions view inj F g regular c)) =
      ∑ j : D.indices, realize i (localPair e D F g localView localInj pairMember i j
        (ConstructedManifoldLocalization.localize e D he functions smooth j c)) := by
  rw [coordinate_action e D he functions smooth zero view inj F g regular localView localInj
    coordinateMember pairMember, map_sum]

include zero in
/-- Finite row summation derives the actual output norm estimate from
per-pair microscopic bounds, without supplying a global block inequality. -/
theorem realized_norm_le (i : D.indices) (c : Core) (bound : D.indices → ℝ)
    (pairBound : ∀ j,
      ‖realize i (localPair e D F g localView localInj pairMember i j
        (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤ bound j) :
    ‖realize i (localCoordinate e D view localView localInj coordinateMember i
      (globalAction functions view inj F g regular c))‖ ≤ ∑ j, bound j := by
  rw [realized_action e D he functions smooth zero view inj F g regular localView localInj
    coordinateMember pairMember realize]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => pairBound j))


/-- The actual global output chart vector, constructed before any norm
bound from the finite-regular realization of the literal weighted output. -/
def outputCore : Core →ₗ[ℂ] (∀ i, B i) := LinearMap.pi fun i =>
  (realize i).comp ((localCoordinate e D view localView localInj coordinateMember i).comp
    (globalAction functions view inj F g regular))

include zero in
/-- Summing the precise local pair coefficients gives a global block bound
in the actual maximum chart norm. Only per-pair microscopic estimates are
inputs; no global word bound is assumed. -/
theorem output_norm_le (c : Core) (Xs Xw : ℝ) (hXs : 0 ≤ Xs) (hXw : 0 ≤ Xw)
    (α β : D.indices → D.indices → ℝ) (hα : ∀ i j, 0 ≤ α i j) (hβ : ∀ i j, 0 ≤ β i j)
    (pairBound : ∀ i j,
      ‖realize i (localPair e D F g localView localInj pairMember i j
        (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤ α i j * Xs + β i j * Xw) :
    ‖outputCore e D functions view inj F g regular localView localInj coordinateMember realize c‖ ≤
      (∑ i, ∑ j, α i j) * Xs + (∑ i, ∑ j, β i j) * Xw := by
  have hA : ∀ i, 0 ≤ ∑ j, α i j := fun i => Finset.sum_nonneg (fun j _ => hα i j)
  have hB : ∀ i, 0 ≤ ∑ j, β i j := fun i => Finset.sum_nonneg (fun j _ => hβ i j)
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun i _ => hA i)) hXs)
    (mul_nonneg (Finset.sum_nonneg (fun i _ => hB i)) hXw))).mpr
  intro i
  have hi := realized_norm_le e D he functions smooth zero view inj F g regular localView localInj
    coordinateMember pairMember realize i c (fun j => α i j * Xs + β i j * Xw) (pairBound i)
  have hsum : (∑ j, (α i j * Xs + β i j * Xw)) = (∑ j, α i j) * Xs + (∑ j, β i j) * Xw := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  rw [hsum] at hi
  exact hi.trans (add_le_add
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ i)) hXs)
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)) hXw))


include zero in
/-- A fixed atlas contributes only its squared cardinality to the common
principal coefficient. This constant is independent of the word length;
the exact summed weak remainders may depend on the chosen finite block. -/
theorem output_norm_le_common_principal (c : Core) (Xs Xw C cost : ℝ)
    (hXs : 0 ≤ Xs) (hXw : 0 ≤ Xw) (hC : 0 ≤ C) (hcost : 0 ≤ cost)
    (remainder : D.indices → D.indices → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j,
      ‖realize i (localPair e D F g localView localInj pairMember i j
        (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤
          (C * cost) * Xs + remainder i j * Xw) :
    ‖outputCore e D functions view inj F g regular localView localInj coordinateMember realize c‖ ≤
      ((Fintype.card D.indices : ℝ) ^ 2 * C * cost) * Xs +
        (∑ i, ∑ j, remainder i j) * Xw := by
  have h := output_norm_le e D he functions smooth zero view inj F g regular localView localInj
    coordinateMember pairMember realize c Xs Xw hXs hXw (fun _ _ => C * cost) remainder
    (fun _ _ => mul_nonneg hC hcost) hR pairBound
  have hc : (∑ _i : D.indices, ∑ _j : D.indices, C * cost) =
      (Fintype.card D.indices : ℝ) ^ 2 * C * cost := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rwa [hc] at h

end LeanShared.RegularChartPairTransfer
