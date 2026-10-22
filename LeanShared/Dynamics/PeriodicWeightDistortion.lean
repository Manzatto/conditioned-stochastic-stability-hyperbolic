module
public import LeanShared.Dynamics.RegularizedLefschetzLocal
public import LeanShared.Geometry.FractionalCompactChartIncrement

/-! Uniform Hölder ratio bounds of the weights `g ∘ T^l`, `l < N`, in chart coordinates at
points of a compact invariant set where `g` is positive. These control the distortion of
the weight products along exponentially close orbit segments. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology NNReal
open LeanShared.HyperbolicBasicSet LeanShared.PeriodicChartConstants
namespace LeanShared.PeriodicChartChains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem exists_weight_ratio (F : ChartFamily E M) (T : M ≃ₜ M) (Λ : Set M) (compactΛ : IsCompact Λ)
    (invariant : ∀ x ∈ Λ, T x ∈ Λ) (N : ℕ) (g : M → ℝ) (continuousG : Continuous g)
    (positive : ∀ x ∈ Λ, 0 < g x) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (regular : ∀ l : ℕ, FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q
      (fun x => g ((T : M → M)^[l] x)))
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ Rw Cw : ℝ, 0 < Rw ∧ 0 ≤ Cw ∧ ∀ x ∈ Λ, ∀ c : F.ι, x ∈ F.good lam c → ∀ l < N,
      ∀ v : E, ‖v‖ ≤ Rw →
        |g ((T : M → M)^[l] ((F.chart c).symm (F.chart c x + v))) / g ((T : M → M)^[l] x) - 1| ≤
          Cw * ‖v‖ ^ q := by
  let := F.fintype
  classical
  have iterateΛ : ∀ l : ℕ, ∀ x ∈ Λ, (T : M → M)^[l] x ∈ Λ := by
    intro l
    induction l with
    | zero => intro x hx; exact hx
    | succ l ih => intro x hx; rw [Function.iterate_succ_apply']; exact invariant _ (ih x hx)
  -- a positive lower bound of g on Λ
  obtain ⟨gmin, hgmin, lower⟩ : ∃ gmin : ℝ, 0 < gmin ∧ ∀ x ∈ Λ, gmin ≤ g x := by
    rcases Λ.eq_empty_or_nonempty with empty | nonempty
    · exact ⟨1, one_pos, fun x hx => by rw [empty] at hx; exact hx.elim⟩
    · obtain ⟨x0, hx0, hmin⟩ := compactΛ.exists_isMinOn nonempty continuousG.continuousOn
      exact ⟨g x0, positive x0 hx0, fun x hx => hmin hx⟩
  -- compact chart patches
  have patch (c : F.ι) : IsCompact (Λ ∩ F.good lam c) ∧ Λ ∩ F.good lam c ⊆ (F.chart c).source :=
    ⟨compactΛ.inter_right (F.isClosed_good lam c), fun x hx =>
      F.closure_domain c (subset_closure (F.good_domain lam hlam c hx.2))⟩
  have each (cl : F.ι × Fin (N + 1)) := (regular cl.2).compact_chart_increment hq hq1
    (F.chart cl.1) (F.mem cl.1) (Λ ∩ F.good lam cl.1) (patch cl.1).1 (patch cl.1).2
  choose r hr C hC bound using each
  obtain ⟨Rw, hRw, hRwle⟩ := exists_uniform_lower r hr
  refine ⟨Rw, (∑ cl, C cl) / gmin, hRw, div_nonneg (Finset.sum_nonneg fun cl _ => hC cl) hgmin.le,
    fun x hx c hc l hl v hv => ?_⟩
  have estimate := bound (c, ⟨l, by omega⟩) x ⟨hx, hc⟩ v (hv.trans (hRwle _))
  have gpos : gmin ≤ g ((T : M → M)^[l] x) := lower _ (iterateΛ l x hx)
  have gpos' : 0 < g ((T : M → M)^[l] x) := hgmin.trans_le gpos
  rw [div_sub_one gpos'.ne', abs_div, abs_of_pos gpos', div_le_iff₀ gpos']
  have hsum : C (c, ⟨l, by omega⟩) ≤ ∑ cl, C cl :=
    Finset.single_le_sum (f := C) (fun cl _ => hC cl) (Finset.mem_univ _)
  have hvq : 0 ≤ ‖v‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  rw [Real.norm_eq_abs] at estimate
  calc |g ((T : M → M)^[l] ((F.chart c).symm (F.chart c x + v))) - g ((T : M → M)^[l] x)|
      ≤ C (c, ⟨l, by omega⟩) * ‖v‖ ^ q := estimate
    _ ≤ (∑ cl, C cl) * ‖v‖ ^ q := mul_le_mul_of_nonneg_right hsum hvq
    _ = (∑ cl, C cl) / gmin * ‖v‖ ^ q * gmin := by field_simp
    _ ≤ (∑ cl, C cl) / gmin * ‖v‖ ^ q * g ((T : M → M)^[l] x) := by
        apply mul_le_mul_of_nonneg_left gpos
        exact mul_nonneg (div_nonneg (Finset.sum_nonneg fun cl _ => hC cl) hgmin.le) hvq

/-- Weight products along orbit segments. -/
@[expose] def weightProduct (T : M → M) (g : M → ℝ) (n : ℕ) (x : M) : ℝ :=
  ∏ l ∈ Finset.range n, g (T^[l] x)

theorem weightProduct_blocks (T : M → M) (g : M → ℝ) (N m : ℕ) (x : M) :
    weightProduct T g (N * m) x =
      ∏ j ∈ Finset.range m, ∏ l ∈ Finset.range N, g (T^[l] ((T^[N])^[j] x)) := by
  induction m with
  | zero => simp [weightProduct]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, weightProduct, weightProduct, Nat.mul_succ,
      Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, add_comm]

end LeanShared.PeriodicChartChains
