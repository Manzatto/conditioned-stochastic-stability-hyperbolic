module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Uniform growth from a robust finite block bound

Submultiplicativity and a single uniform block length control arbitrary
words. Continuity of the fixed-length word functional then constructs a
generator neighborhood from one strict deterministic block estimate. This
does not assume the final arbitrary-word estimate as a background result.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace LeanShared.UniformWordGrowth

variable {G : Type*}

theorem le_oneStep_pow (q : List G → ℝ) (hq : ∀ word, 0 ≤ q word) (hε : q [] ≤ 1)
    (hsub : ∀ u v, q (u ++ v) ≤ q u * q v)
    (M : ℝ) (hM : 0 ≤ M) (hstep : ∀ a, q [a] ≤ M) (word : List G) :
    q word ≤ M ^ word.length := by
  induction word with
  | nil => simpa using hε
  | cons a word ih =>
      calc
        q (a :: word) ≤ q [a] * q word := hsub [a] word
        _ ≤ M * (M ^ word.length) := mul_le_mul (hstep a) ih (hq word) hM
        _ = M ^ (a :: word).length := by simp [pow_succ, mul_comm]

/-- The explicit constant is the sum of the possible normalized remainder
length bounds, including the empty remainder. -/
theorem uniform_growth (q : List G → ℝ) (hq : ∀ word, 0 ≤ q word)
    (hε : q [] ≤ 1) (hsub : ∀ u v, q (u ++ v) ≤ q u * q v)
    (M : ℝ) (hM : 0 ≤ M) (hstep : ∀ a, q [a] ≤ M)
    (N : ℕ) (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : ∀ word : List G, word.length = N → q word ≤ ρ ^ N) :
    0 ≤ ∑ r ∈ Finset.range N, (M / ρ) ^ r ∧
      ∀ word : List G, q word ≤ (∑ r ∈ Finset.range N, (M / ρ) ^ r) * ρ ^ word.length := by
  let C : ℝ := ∑ r ∈ Finset.range N, (M / ρ) ^ r
  have hC : 0 ≤ C := Finset.sum_nonneg fun r _ => pow_nonneg (div_nonneg hM hρ.le) r
  refine ⟨hC, ?_⟩
  suffices ∀ n : ℕ, ∀ word : List G, word.length = n → q word ≤ C * ρ ^ word.length by
    exact fun word => this word.length word rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro word hlen
    by_cases hn : n < N
    · have hterm : (M / ρ) ^ word.length ≤ C := by
        apply Finset.single_le_sum (fun r _ => pow_nonneg (div_nonneg hM hρ.le) r)
        exact Finset.mem_range.mpr (hlen ▸ hn)
      calc
        q word ≤ M ^ word.length := le_oneStep_pow q hq hε hsub M hM hstep word
        _ = (M / ρ) ^ word.length * ρ ^ word.length := by
          rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ.ne')]
        _ ≤ C * ρ ^ word.length := mul_le_mul_of_nonneg_right hterm (pow_nonneg hρ.le _)
    · have hNn : N ≤ word.length := hlen ▸ Nat.le_of_not_gt hn
      have htake : (word.take N).length = N := by simp [List.length_take, Nat.min_eq_left hNn]
      have hdrop : (word.drop N).length < n := by simp only [List.length_drop]; omega
      have hi := ih _ hdrop (word.drop N) rfl
      calc
        q word = q (word.take N ++ word.drop N) := by rw [List.take_append_drop]
        _ ≤ q (word.take N) * q (word.drop N) := hsub _ _
        _ ≤ ρ ^ N * (C * ρ ^ (word.drop N).length) :=
          mul_le_mul (hblock _ htake) hi (hq _) (pow_nonneg hρ.le _)
        _ = C * ρ ^ word.length := by
          rw [List.length_drop, ← mul_assoc, mul_comm (ρ ^ N) C, mul_assoc, ← pow_add,
            Nat.add_sub_of_le hNn]

variable [TopologicalSpace G]

/-- A finite product neighborhood of a constant word contains a product of
one common open generator neighborhood. Only continuity at that word is
required. -/
theorem exists_open_uniform_box (N : ℕ) (T : G) (Q : (Fin N → G) → ℝ)
    (hQ : ContinuousAt Q (fun _ => T)) (b : ℝ) (hb : Q (fun _ => T) < b) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧
      ∀ word : Fin N → G, (∀ i, word i ∈ W) → Q word < b := by
  have hevent : Q ⁻¹' Iio b ∈ 𝓝 (fun _ : Fin N => T) := hQ (gt_mem_nhds hb)
  obtain ⟨O, hOsub, hO, hTO⟩ := mem_nhds_iff.mp hevent
  obtain ⟨U, hU, hUsub⟩ := isOpen_pi_iff'.mp hO (fun _ => T) hTO
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite (fun i => (hU i).1),
    mem_iInter.mpr (fun i => (hU i).2), ?_⟩
  intro word hword
  exact hOsub (hUsub (fun i _ => mem_iInter.mp (hword i) i))

/-- A strict deterministic block estimate is robust for every nearby word
of the same length, rather than just for powers of a single nearby map. -/
theorem exists_robust_block_neighborhood (q : List G → ℝ) (N : ℕ) (T : G)
    (ρ : ℝ) (hQ : ContinuousAt (fun word : Fin N → G => q (List.ofFn word)) (fun _ => T))
    (hdet : q (List.replicate N T) < ρ ^ N) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ ∀ word : List G,
      word.length = N → (∀ a ∈ word, a ∈ W) → q word ≤ ρ ^ N := by
  obtain ⟨W, hW, hTW, hb⟩ := exists_open_uniform_box N T
    (fun word => q (List.ofFn word)) hQ (ρ ^ N) (by simpa only [List.ofFn_const] using hdet)
  refine ⟨W, hW, hTW, ?_⟩
  intro word hlen hword
  subst N
  have hh := hb word.get (fun i => hword _ (List.get_mem word i))
  simpa only [List.ofFn_get] using hh.le

/-- Simultaneous one-step and block robustness gives a uniform arbitrary
word bound on one open generator neighborhood. The final constant is
computed from the resulting one-step bound and the prescribed rate. -/
theorem exists_uniform_growth_neighborhood (q : List G → ℝ)
    (hq : ∀ word, 0 ≤ q word) (hε : q [] ≤ 1)
    (hsub : ∀ u v, q (u ++ v) ≤ q u * q v)
    (N : ℕ) (hN : 0 < N) (T : G) (ρ : ℝ) (hρ : 0 < ρ)
    (hQ : ContinuousAt (fun word : Fin N → G => q (List.ofFn word)) (fun _ => T))
    (hdet : q (List.replicate N T) < ρ ^ N)
    (hstep : ContinuousAt (fun a => q [a]) T) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ word : List G, (∀ a ∈ word, a ∈ W) → q word ≤ C * ρ ^ word.length := by
  obtain ⟨B, hB, hTB, hblock⟩ := exists_robust_block_neighborhood q N T ρ hQ hdet
  let M := q [T] + 1
  have hM : 0 ≤ M := (hq [T]).trans (le_add_of_nonneg_right zero_le_one)
  have hevent : {a | q [a] < M} ∈ 𝓝 T := hstep (gt_mem_nhds (lt_add_one (q [T])))
  obtain ⟨A, hAsub, hA, hTA⟩ := mem_nhds_iff.mp hevent
  let W := B ∩ A
  let p : List W → ℝ := fun word => q (word.map Subtype.val)
  have hp : ∀ word, 0 ≤ p word := fun word => hq _
  have hpε : p [] ≤ 1 := hε
  have hpsub : ∀ u v, p (u ++ v) ≤ p u * p v := by
    intro u v
    simpa only [p, List.map_append] using hsub (u.map Subtype.val) (v.map Subtype.val)
  have hpstep : ∀ a : W, p [a] ≤ M := fun a => (hAsub a.property.2).le
  have hpblock : ∀ word : List W, word.length = N → p word ≤ ρ ^ N := by
    intro word hlen
    apply hblock (word.map Subtype.val) (by simpa using hlen)
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact b.property.1
  obtain ⟨hC, hbound⟩ := uniform_growth p hp hpε hpsub M hM hpstep N hN ρ hρ hpblock
  refine ⟨W, hB.inter hA, ⟨hTB, hTA⟩, _, hC, ?_⟩
  intro word hword
  let lifted : List W := word.attach.map (fun a => ⟨a.val, hword a.val a.property⟩)
  have he : lifted.map Subtype.val = word := by
    simp only [lifted, List.map_map, Function.comp_def, List.attach_map_subtype_val]
  have hh := hbound lifted
  simpa only [p, he, lifted, List.length_map, List.length_attach] using hh

end LeanShared.UniformWordGrowth
