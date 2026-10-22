module

public import LeanShared.Dynamics.ControlledPlaqueClosure
public import LeanShared.Dynamics.PressureBlocks
public import ConditionedStochasticStabilityHyperbolic.Global.StableAccessibility
import Mathlib.Tactic.Linarith

/-!
# Heteroclinic connections propagate actual controlled positivity

A fixed local noise-image radius and the deterministic noise parameter turn
past/future convergence of a heteroclinic orbit into positivity on its source
basic set. Transitivity is used only on that basic set. This is not an assumed
finite control from one basic set to another: the control steps are derived
from ordinary orbit approach and the local image inclusion.
-/

@[expose] public noncomputable section

open Set

namespace ConditionedStochasticStabilityHyperbolic.Global.HeteroclinicAccessibility

open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X]

omit [MetricSpace X] in
private theorem pos_of_forward_iterate (T : X → X) (F : X × Ω → X) (ω₀ : Ω)
    (hzero : ∀ x, F (x, ω₀) = T x) (U : Set X) (h : X → ℝ)
    (hstep : ∀ x ∈ U, ∀ ω, F (x, ω) ∈ U → 0 < h (F (x, ω)) → 0 < h x)
    (n : ℕ) (x : X) (hlive : ∀ i, i ≤ n → T^[i] x ∈ U)
    (hend : 0 < h (T^[n] x)) : 0 < h x := by
  induction n generalizing x with
  | zero => simpa using hend
  | succ n ih =>
      apply hstep x (hlive 0 (Nat.zero_le _)) ω₀
      · rw [hzero]
        exact hlive 1 (Nat.succ_le_succ (Nat.zero_le _))
      · rw [hzero]
        apply ih (T x)
        · intro i hi
          rw [← Function.iterate_succ_apply]
          exact hlive (i + 1) (Nat.succ_le_succ hi)
        · simpa only [Function.iterate_succ_apply] using hend

/-- A single positive point and local noise reachability give positivity on
an entire transitive basic set, without assuming its individual orbits dense. -/
theorem positive_on_transitive_set
    (T : X → X) (F : X × Ω → X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U Λ : Set X) (hΛU : Λ ⊆ U) (hinvariant : MapsTo T Λ Λ)
    (htrans : forwardTransitiveOn T Λ) (h : X → ℝ) (hhc : Continuous h)
    (hstep : ∀ x ∈ U, ∀ ω, F (x, ω) ∈ U → 0 < h (F (x, ω)) → 0 < h x)
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (hseed : ∃ q ∈ Λ, 0 < h q) : ∀ p ∈ Λ, 0 < h p := by
  intro p hp
  let W := Metric.ball (T p) δ
  have hW : IsOpen W := Metric.isOpen_ball
  have hnonempty : (Λ ∩ W).Nonempty :=
    ⟨T p, hinvariant hp, Metric.mem_ball_self hδ⟩
  obtain ⟨q, hq, hhq⟩ := hseed
  have hclosure := htrans W hW hnonempty hq
  obtain ⟨a, hapos, ha⟩ := mem_closure_iff.1 hclosure {z | 0 < h z}
    (isOpen_lt continuous_const hhc) hhq
  obtain ⟨n, b, hb, rfl⟩ := mem_iUnion.mp ha
  have hbpos : 0 < h b := pos_of_forward_iterate T F ω₀ hzero U h hstep n b
    (fun i _hi => hΛU (hinvariant.iterate i hb.1)) hapos
  have hnear : dist (T p) b < δ := by
    simpa only [W, Metric.mem_ball, dist_comm] using hb.2
  obtain ⟨ω, hω⟩ := himage p (hΛU hp) b (hΛU hb.1) hnear
  apply hstep p (hΛU hp) ω
  · rw [hω]
    exact hΛU hb.1
  · rwa [hω]

/-- The future of a heteroclinic point is steered to the positive target;
its past then supplies a positive source point. Transitivity propagates that
seed to every source state. -/
theorem positive_on_source_of_heteroclinic
    (T : X ≃ₜ X) (F : X × Ω → X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U A B : Set X) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hTA : MapsTo T A A) (hinvA : MapsTo T.symm A A)
    (htrans : forwardTransitiveOn T A) (h : X → ℝ) (hhc : Continuous h)
    (hstep : ∀ x ∈ U, ∀ ω, F (x, ω) ∈ U → 0 < h (F (x, ω)) → 0 < h x)
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (hBpos : ∀ y ∈ B, 0 < h y) (z : X)
    (hforwardlive : ∀ n : ℕ, (T : X → X)^[n] z ∈ U)
    (hbackwardlive : ∀ n : ℕ, (T.symm : X → X)^[n] z ∈ U)
    (hfuture : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ B,
      dist ((T : X → X)^[n + 1] z) y < r)
    (hpast : ∀ r : ℝ, 0 < r → ∃ m : ℕ, ∃ y ∈ A,
      dist ((T.symm : X → X)^[m] z) y < r) :
    ∀ p ∈ A, 0 < h p := by
  obtain ⟨n, b, hb, hnear⟩ := hfuture δ hδ
  have hn : dist (T ((T : X → X)^[n] z)) b < δ := by
    simpa only [Function.iterate_succ_apply'] using hnear
  obtain ⟨ω, hω⟩ := himage _ (hforwardlive n) b (hBU hb) hn
  have hzn : 0 < h ((T : X → X)^[n] z) := by
    apply hstep _ (hforwardlive n) ω
    · rw [hω]
      exact hBU hb
    · rw [hω]
      exact hBpos b hb
  have hz : 0 < h z := pos_of_forward_iterate T F ω₀ hzero U h hstep n z
    (fun i _hi => hforwardlive i) hzn
  have hback (m : ℕ) : 0 < h ((T.symm : X → X)^[m] z) := by
    induction m with
    | zero => exact hz
    | succ m ih =>
        apply hstep _ (hbackwardlive (m + 1)) ω₀
        · rw [hzero, Function.iterate_succ_apply', T.apply_symm_apply]
          exact hbackwardlive m
        · rw [hzero, Function.iterate_succ_apply', T.apply_symm_apply]
          exact ih
  obtain ⟨m, a, ha, hnearA⟩ := hpast δ hδ
  have hnearA' : dist (T (T.symm a)) ((T.symm : X → X)^[m] z) < δ := by
    simpa only [T.apply_symm_apply, dist_comm] using hnearA
  obtain ⟨ω', hω'⟩ := himage (T.symm a) (hAU (hinvA ha))
    ((T.symm : X → X)^[m] z) (hbackwardlive m) hnearA'
  have hapos : 0 < h (T.symm a) := by
    apply hstep _ (hAU (hinvA ha)) ω'
    · rw [hω']
      exact hbackwardlive m
    · rw [hω']
      exact hback m
  exact positive_on_transitive_set T F ω₀ hzero U A hAU hTA htrans h hhc hstep hδ himage
    ⟨T.symm a, hinvA ha, hapos⟩

/-- Ordinary stable/unstable orbit data for a heteroclinic edge. The witness
contains no controlled paths and no eigenfunction positivity conclusion. -/
structure HeteroclinicWitness (T : X ≃ₜ X) (U A B : Set X) where
  point : X
  forward_live : ∀ n : ℕ, (T : X → X)^[n] point ∈ U
  backward_live : ∀ n : ℕ, (T.symm : X → X)^[n] point ∈ U
  future : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ B,
    dist ((T : X → X)^[n + 1] point) y < r
  past : ∀ r : ℝ, 0 < r → ∃ m : ℕ, ∃ y ∈ A,
    dist ((T.symm : X → X)^[m] point) y < r

/-- Positivity propagates through the actual reflexive-transitive
heteroclinic relation used by the pressure ordering. -/
theorem positive_along_graph_reachability {I : Type*}
    (T : X ≃ₜ X) (F : X × Ω → X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U : Set X) (Λ : I → Set X) (hΛU : ∀ i, Λ i ⊆ U)
    (hT : ∀ i, MapsTo T (Λ i) (Λ i)) (hinv : ∀ i, MapsTo T.symm (Λ i) (Λ i))
    (htrans : ∀ i, forwardTransitiveOn T (Λ i))
    (h : X → ℝ) (hhc : Continuous h)
    (hstep : ∀ x ∈ U, ∀ ω, F (x, ω) ∈ U → 0 < h (F (x, ω)) → 0 < h x)
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (edge : I → I → Prop)
    (hedge : ∀ i j, edge i j → HeteroclinicWitness T U (Λ i) (Λ j))
    {i root : I} (hreach : Relation.ReflTransGen edge i root)
    (hroot : ∀ p ∈ Λ root, 0 < h p) : ∀ p ∈ Λ i, 0 < h p := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact hroot
  | @head i j hij _hreach ih =>
      let w := hedge i j hij
      exact positive_on_source_of_heteroclinic T F ω₀ hzero U (Λ i) (Λ j)
        (hΛU i) (hΛU j) (hT i) (hinv i) (htrans i) h hhc hstep hδ himage ih
        w.point w.forward_live w.backward_live w.future w.past

/-- Every basic set assigned to a selected pressure root is positive for
its leading eigenfunction. The graph algorithm supplies reachability; the
heteroclinic witness and actual noise image supply the control mechanism. -/
theorem positive_on_pressure_predecessor_block {I : Type*}
    (T : X ≃ₜ X) (F : X × Ω → X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (U : Set X) (Λ : I → Set X) (hΛU : ∀ i, Λ i ⊆ U)
    (hT : ∀ i, MapsTo T (Λ i) (Λ i)) (hinv : ∀ i, MapsTo T.symm (Λ i) (Λ i))
    (htrans : ∀ i, forwardTransitiveOn T (Λ i))
    (h : X → ℝ) (hhc : Continuous h)
    (hstep : ∀ x ∈ U, ∀ ω, F (x, ω) ∈ U → 0 < h (F (x, ω)) → 0 < h x)
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U, ∀ y ∈ U, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (edge : I → I → Prop)
    (hedge : ∀ i j, edge i j → HeteroclinicWitness T U (Λ i) (Λ j))
    (R : Finset I) (root i : I)
    (hi : i ∈ LeanShared.PressureBlocks.predecessorBlock edge R root)
    (hroot : ∀ p ∈ Λ root, 0 < h p) : ∀ p ∈ Λ i, 0 < h p := by
  exact positive_along_graph_reachability T F ω₀ hzero U Λ hΛU hT hinv htrans h hhc
    hstep hδ himage edge hedge ((LeanShared.PressureBlocks.mem_predecessorBlock edge R root i).mp hi).2 hroot

end ConditionedStochasticStabilityHyperbolic.Global.HeteroclinicAccessibility
