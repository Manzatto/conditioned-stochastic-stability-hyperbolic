module

public import LeanShared.Dynamics.IsolatingNeighborhood
public import LeanShared.Topology.PerturbationSeparation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The neighborhoods of Lemmas `lem:set_U` and `lem:set_U_stoch`

The paper's finite maximum is encoded as a condition for every `j : Fin N`.
The weight `(2 ^ (1 / N)) ^ j` is exactly `2 ^ (j / N)` over the reals.
No hyperbolicity, differentiability, spectral theory, or probabilistic axioms
are needed for these lemmas.
-/

@[expose] public section

open Set Metric Function

namespace ConditionedStochasticStabilityHyperbolic

variable {X : Type*} [MetricSpace X]

/-- The one-step geometric weight in the paper's construction. -/
noncomputable def stepWeight (N : ℕ) : ℝ := (2 : ℝ) ^ (N : ℝ)⁻¹

theorem stepWeight_gt_one {N : ℕ} (hN : 0 < N) : 1 < stepWeight N := by
  exact Real.one_lt_rpow (by norm_num) (inv_pos.mpr (Nat.cast_pos.mpr hN))

theorem stepWeight_pow {N : ℕ} (hN : 0 < N) : stepWeight N ^ N = 2 := by
  exact Real.rpow_inv_natCast_pow (by norm_num) (Nat.ne_of_gt hN)

/-- This identifies our weights with the literal weights in the manuscript. -/
theorem stepWeight_pow_eq (N j : ℕ) :
    stepWeight N ^ j = (2 : ℝ) ^ ((j : ℝ) / (N : ℝ)) := by
  rw [stepWeight, ← Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

/-- The strict finite-orbit inequalities defining the open neighborhood. -/
noncomputable def orbitNeighborhood (T : X → X) (Λ : Set X) (ρ : ℝ) (N : ℕ) : Set X :=
  {x | ∀ j : Fin N, stepWeight N ^ j.val * infDist (T^[j.val] x) Λ < ρ}

theorem isOpen_orbitNeighborhood {T : X → X} (hT : Continuous T)
    (Λ : Set X) (ρ : ℝ) (N : ℕ) : IsOpen (orbitNeighborhood T Λ ρ N) := by
  have heq : orbitNeighborhood T Λ ρ N =
      ⋂ j : Fin N, {x | stepWeight N ^ j.val * infDist (T^[j.val] x) Λ < ρ} := by
    ext x
    simp [orbitNeighborhood]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (continuous_const.mul
    ((continuous_infDist_pt Λ).comp (hT.iterate j.val))) continuous_const

theorem closure_orbitNeighborhood_le {T : X → X} (hT : Continuous T)
    {Λ : Set X} {ρ : ℝ} {N : ℕ} {x : X}
    (hx : x ∈ closure (orbitNeighborhood T Λ ρ N)) (j : Fin N) :
    stepWeight N ^ j.val * infDist (T^[j.val] x) Λ ≤ ρ := by
  have hclosed : IsClosed {x : X |
      stepWeight N ^ j.val * infDist (T^[j.val] x) Λ ≤ ρ} :=
    isClosed_le (continuous_const.mul
      ((continuous_infDist_pt Λ).comp (hT.iterate j.val))) continuous_const
  have hsub : orbitNeighborhood T Λ ρ N ⊆
      {x : X | stepWeight N ^ j.val * infDist (T^[j.val] x) Λ ≤ ρ} :=
    fun _ hy => (hy j).le
  exact closure_minimal hsub hclosed hx

theorem orbitNeighborhood_subset_thickening {T : X → X} {Λ : Set X}
    (hΛ : Λ.Nonempty) (ρ : ℝ) {N : ℕ} (hN : 0 < N) :
    orbitNeighborhood T Λ ρ N ⊆ thickening ρ Λ := by
  intro x hx
  apply (mem_thickening_iff_infDist_lt hΛ).mpr
  simpa using hx ⟨0, hN⟩

variable [CompactSpace X]

/-- Lemma `lem:set_U`: an open neighborhood with strict nonreturn along
the local stable set. The isolated-core hypothesis is the only dynamical input. -/
theorem exists_orbitNeighborhood (T : X ≃ₜ X) {V Λ : Set X}
    (hΛ : Λ.Nonempty) (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closure (thickening ρ Λ) ⊆ V) :
    ∃ N : ℕ, 0 < N ∧
      IsOpen (orbitNeighborhood T Λ ρ N) ∧
      Λ ⊆ orbitNeighborhood T Λ ρ N ∧
      closure (orbitNeighborhood T Λ ρ N) ⊆ V ∧
      (T '' closure (orbitNeighborhood T Λ ρ N)) ∩
        LeanShared.forwardTrapped T (closure V) ⊆ orbitNeighborhood T Λ ρ N := by
  obtain ⟨N, hN, htail⟩ := LeanShared.exists_pos_stable_tail_subset T
    (K := closure V) (U := thickening (ρ / 2) Λ)
    isClosed_closure.isCompact isOpen_thickening
    (by rw [hcore]; exact self_subset_thickening (half_pos hρ) Λ)
  have hUball := orbitNeighborhood_subset_thickening (T := (T : X → X)) hΛ ρ hN
  have hUV : closure (orbitNeighborhood T Λ ρ N) ⊆ V :=
    (closure_mono hUball).trans hball
  refine ⟨N, hN, isOpen_orbitNeighborhood T.continuous Λ ρ N, ?_, hUV, ?_⟩
  · intro x hx j
    have hxcore : x ∈ LeanShared.isolatedCore T (closure V) := by rwa [hcore]
    have hjΛ : (T : X → X)^[j.val] x ∈ Λ := by
      rw [← hcore]
      exact LeanShared.iterate_mem_isolatedCore T (closure V) hxcore j.val
    simpa only [infDist_zero_of_mem hjΛ, mul_zero] using hρ
  · rintro y ⟨⟨x, hx, rfl⟩, hTx⟩ j
    have hxstable : x ∈ LeanShared.forwardTrapped T (closure V) :=
      LeanShared.mem_forwardTrapped_of_mem_of_image_mem (subset_closure (hUV hx)) hTx
    have hq : 1 < stepWeight N := stepWeight_gt_one hN
    have hqpos : 0 < stepWeight N := lt_trans zero_lt_one hq
    have hqρ : ρ < stepWeight N * ρ := by nlinarith
    have hshift : (T : X → X)^[j.val] (T x) = (T : X → X)^[j.val + 1] x :=
      (iterate_succ_apply T j.val x).symm
    rw [hshift]
    have hbound : stepWeight N ^ (j.val + 1) *
        infDist ((T : X → X)^[j.val + 1] x) Λ ≤ ρ := by
      by_cases hj : j.val + 1 < N
      · exact closure_orbitNeighborhood_le T.continuous hx ⟨j.val + 1, hj⟩
      · have hlast : j.val + 1 = N := by omega
        rw [hlast, stepWeight_pow hN]
        have hdist : infDist ((T : X → X)^[N] x) Λ < ρ / 2 :=
          (mem_thickening_iff_infDist_lt hΛ).mp (htail ⟨x, hxstable, rfl⟩)
        linarith
    rw [pow_succ] at hbound
    nlinarith

/-- Lemma `lem:set_U_stoch`, stated uniformly for arbitrary maps close to `T`.
This is stronger than an almost-sure assertion about a particular noise law. -/
theorem exists_uniform_orbit_nonreturn (T : X ≃ₜ X) {V Λ : Set X}
    (hΛ : Λ.Nonempty) (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closure (thickening ρ Λ) ⊆ V) :
    ∃ N : ℕ, 0 < N ∧
      IsOpen (orbitNeighborhood T Λ ρ N) ∧
      Λ ⊆ orbitNeighborhood T Λ ρ N ∧
      closure (orbitNeighborhood T Λ ρ N) ⊆ V ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
        (∀ x ∈ closure (orbitNeighborhood T Λ ρ N), dist (F x) (T x) < δ) →
        ∀ x ∈ closure (orbitNeighborhood T Λ ρ N),
          F x ∉ thickening δ (LeanShared.forwardTrapped T (closure V)) \
            orbitNeighborhood T Λ ρ N := by
  obtain ⟨N, hN, hU, hΛU, hUV, hsep⟩ := exists_orbitNeighborhood T hΛ hcore hρ hball
  refine ⟨N, hN, hU, hΛU, hUV, ?_⟩
  exact LeanShared.exists_uniform_nonreturn T.continuous isClosed_closure.isCompact
    (LeanShared.isClosed_forwardTrapped T.continuous isClosed_closure) hU hsep

end ConditionedStochasticStabilityHyperbolic
