module

public import LeanShared.Analysis.UniformWordGrowth
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Robust two-norm blocks from upper semicontinuous coefficients

Only the coefficients of the actual fixed-length local estimate must be
upper semicontinuous. Neither continuity in the strong operator norm nor
submultiplicativity of an ordinary operator norm is assumed. The local
anisotropic estimate and its identified principal/remainder coefficients
remain explicit inputs; the common open generator neighborhood is derived.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.RobustTwoNormBlock

variable {G : Type*} [TopologicalSpace G]

/-- A finite product neighborhood of a constant word contains all tuples
from a common open neighborhood of the generator. -/
theorem exists_open_box_of_mem_nhds (N : ℕ) (T : G) (O : Set (Fin N → G))
    (hO : O ∈ 𝓝 (fun _ => T)) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧
      ∀ word : Fin N → G, (∀ i, word i ∈ W) → word ∈ O := by
  obtain ⟨U, hUO, hU, hTU⟩ := mem_nhds_iff.mp hO
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU (fun _ => T) hTU
  refine ⟨⋂ i, V i, isOpen_iInter_of_finite (fun i => (hV i).1),
    mem_iInter.mpr (fun i => (hV i).2), ?_⟩
  intro word hword
  exact hUO (hVU (fun i _ => mem_iInter.mp (hword i) i))

/-- The robust tuple estimate, including a possibly smaller neighborhood
where the cited local transfer estimate is valid. -/
theorem exists_robust_tuple_estimate {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (N : ℕ) (T : G) (P : List G → E →L[𝕜] E) (ι : E →L[𝕜] F)
    (a b : (Fin N → G) → ℝ)
    (ha : UpperSemicontinuousAt a (fun _ => T))
    (hb : UpperSemicontinuousAt b (fun _ => T))
    (ρ : ℝ) (hstrict : a (fun _ => T) < ρ ^ N)
    (O : Set (Fin N → G)) (hO : O ∈ 𝓝 (fun _ => T))
    (hlocal : ∀ word ∈ O, ∀ x : E,
      ‖P (List.ofFn word) x‖ ≤ a word * ‖x‖ + b word * ‖ι x‖) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ word : Fin N → G, (∀ i, word i ∈ W) → word ∈ O ∧
        ∀ x : E, ‖P (List.ofFn word) x‖ ≤ ρ ^ N * ‖x‖ + B * ‖ι x‖ := by
  let B := max (b (fun _ => T) + 1) 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbB : b (fun _ => T) < B :=
    (lt_add_one _).trans_le (le_max_left _ _)
  have hevent : {word | word ∈ O ∧ a word < ρ ^ N ∧ b word < B} ∈ 𝓝 (fun _ => T) := by
    filter_upwards [hO, ha _ hstrict, hb _ hbB] with word hword haw hbw
    exact ⟨hword, haw, hbw⟩
  obtain ⟨W, hW, hTW, hbox⟩ := exists_open_box_of_mem_nhds N T _ hevent
  refine ⟨W, hW, hTW, B, hB, ?_⟩
  intro word hword
  obtain ⟨hwO, haw, hbw⟩ := hbox word hword
  refine ⟨hwO, fun x => (hlocal word hwO x).trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_right haw.le (norm_nonneg x))
    (mul_le_mul_of_nonneg_right hbw.le (norm_nonneg _))

/-- Exact list-word form consumed by finite-block Lasota--Yorke iteration.
All words of length `N` over the derived open generator neighborhood obey
one common strong coefficient and one common nonnegative weak remainder. -/
theorem exists_robust_list_estimate {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (N : ℕ) (T : G) (P : List G → E →L[𝕜] E) (ι : E →L[𝕜] F)
    (a b : (Fin N → G) → ℝ)
    (ha : UpperSemicontinuousAt a (fun _ => T))
    (hb : UpperSemicontinuousAt b (fun _ => T))
    (ρ : ℝ) (hstrict : a (fun _ => T) < ρ ^ N)
    (O : Set (Fin N → G)) (hO : O ∈ 𝓝 (fun _ => T))
    (hlocal : ∀ word ∈ O, ∀ x : E,
      ‖P (List.ofFn word) x‖ ≤ a word * ‖x‖ + b word * ‖ι x‖) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ word : List G, word.length = N → (∀ a ∈ word, a ∈ W) →
        ∀ x : E, ‖P word x‖ ≤ ρ ^ N * ‖x‖ + B * ‖ι x‖ := by
  obtain ⟨W, hW, hTW, B, hB, htuple⟩ :=
    exists_robust_tuple_estimate N T P ι a b ha hb ρ hstrict O hO hlocal
  refine ⟨W, hW, hTW, B, hB, ?_⟩
  intro word hlen hword x
  subst N
  simpa only [List.ofFn_get] using
    (htuple word.get (fun i => hword _ (List.get_mem word i))).2 x

end LeanShared.RobustTwoNormBlock
