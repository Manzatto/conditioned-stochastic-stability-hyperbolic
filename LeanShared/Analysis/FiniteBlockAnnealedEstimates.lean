module

public import LeanShared.Analysis.TwoNormBlockIteration
public import LeanShared.Analysis.AnnealedOperatorBounds
public import LeanShared.Analysis.RobustTwoNormBlock

/-!
# Actual annealed estimates from finite-block deterministic control

One-step strong and weak bounds control short words. A robust estimate at a
single block length is iterated with its weak error retained, then averaged
over the actual independent noise words. No arbitrary-word Lasota–Yorke
estimate or operator-valued Bochner measurability is an input.
-/

@[expose] public noncomputable section

open MeasureTheory
open Set Filter
open scoped BigOperators Topology

namespace LeanShared.FiniteBlockAnnealedEstimates

open AnnealedOperatorBounds

variable {Ω E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def listWord (A : Ω → E →L[ℂ] E) : List Ω → E →L[ℂ] E
  | [] => 1
  | a :: word => (A a).comp (listWord A word)

theorem listWord_append (A : Ω → E →L[ℂ] E) (u v : List Ω) (x : E) :
    listWord A (u ++ v) x = listWord A u (listWord A v x) := by
  induction u with
  | nil => simp [listWord]
  | cons a u ih => simpa only [List.cons_append, listWord, ContinuousLinearMap.comp_apply] using congrArg (A a) ih

theorem listWord_map {G : Type*} (A : G → E →L[ℂ] E) (ζ : Ω → G) (word : List Ω) :
    listWord (fun ω => A (ζ ω)) word = listWord A (word.map ζ) := by
  induction word with
  | nil => rfl
  | cons a word ih => simpa only [List.map_cons, listWord] using congrArg ((A (ζ a)).comp) ih

theorem strong_word_bound (A : Ω → E →L[ℂ] E) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ ω, ‖A ω‖ ≤ L) (word : List Ω) (x : E) :
    ‖listWord A word x‖ ≤ L ^ word.length * ‖x‖ := by
  induction word with
  | nil => simp [listWord]
  | cons a word ih =>
      calc
        ‖listWord A (a :: word) x‖ ≤ L * ‖listWord A word x‖ :=
          ((A a).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA a) (norm_nonneg _))
        _ ≤ L * (L ^ word.length * ‖x‖) := mul_le_mul_of_nonneg_left ih hL
        _ = L ^ (a :: word).length * ‖x‖ := by simp [pow_succ]; ring

theorem weak_word_bound (A : Ω → E →L[ℂ] E) (ι : E →L[ℂ] F)
    (M : ℝ) (hM : 0 ≤ M) (hweak : ∀ ω x, ‖ι (A ω x)‖ ≤ M * ‖ι x‖)
    (word : List Ω) (x : E) :
    ‖ι (listWord A word x)‖ ≤ M ^ word.length * ‖ι x‖ := by
  induction word with
  | nil => simp [listWord]
  | cons a word ih =>
      calc
        ‖ι (listWord A (a :: word) x)‖ ≤ M * ‖ι (listWord A word x)‖ := hweak a _
        _ ≤ M * (M ^ word.length * ‖ι x‖) := mul_le_mul_of_nonneg_left ih hM
        _ = M ^ (a :: word).length * ‖ι x‖ := by simp [pow_succ]; ring

def noiseWordList : (n : ℕ) → NoiseWords Ω n → List Ω
  | 0, _ => []
  | n + 1, p => p.1 :: noiseWordList n p.2

@[simp]
theorem noiseWordList_length (n : ℕ) (word : NoiseWords Ω n) :
    (noiseWordList n word).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih word.2)

variable [CompleteSpace E]

/-- The weak power estimate for the actual average follows from its
one-step weak bound. No operator on an independently supplied weak space or
arbitrary-word growth bound is assumed. -/
theorem annealed_weak_power_bound [MeasurableSpace Ω] [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E →L[ℂ] E)
    (hmeas : ∀ x, AEStronglyMeasurable (fun ω => A ω x) μ)
    (L : ℝ) (hA : ∀ ω, ‖A ω‖ ≤ L)
    (ι : E →L[ℂ] F) (M : ℝ) (hM : 0 ≤ M)
    (hweak : ∀ ω x, ‖ι (A ω x)‖ ≤ M * ‖ι x‖) :
    ∀ n x, ‖ι ((pointwiseAnnealed μ A hmeas L hA ^ n) x)‖ ≤ M ^ n * ‖ι x‖ := by
  have hstep (x : E) : ‖ι (pointwiseAnnealed μ A hmeas L hA x)‖ ≤ M * ‖ι x‖ := by
    rw [pointwiseAnnealed_apply,
      ← ι.integral_comp_comm (random_apply_integrable μ A hmeas L hA x)]
    simpa using norm_integral_le_of_norm_le_const (ae_of_all μ fun ω => hweak ω x)
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    calc
      ‖ι ((pointwiseAnnealed μ A hmeas L hA ^ (n + 1)) x)‖ =
          ‖ι (pointwiseAnnealed μ A hmeas L hA ((pointwiseAnnealed μ A hmeas L hA ^ n) x))‖ := by
        rw [pow_succ']
        rfl
      _ ≤ M * ‖ι ((pointwiseAnnealed μ A hmeas L hA ^ n) x)‖ := hstep _
      _ ≤ M * (M ^ n * ‖ι x‖) := mul_le_mul_of_nonneg_left (ih x) hM
      _ = M ^ (n + 1) * ‖ι x‖ := by rw [pow_succ]; ring

omit [CompleteSpace E] in
theorem listWord_noiseWordList (A : Ω → E →L[ℂ] E) (n : ℕ) (word : NoiseWords Ω n) :
    listWord A (noiseWordList n word) = operatorWord A n word := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [noiseWordList, listWord, operatorWord] using congrArg ((A word.1).comp) (ih word.2)

/-- The actual pointwise annealed operator satisfies a two-norm power bound
from just uniform one-step bounds and one robust deterministic block length. -/
theorem annealed_twoNorm_bound [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E →L[ℂ] E)
    (hmeas : ∀ x, AEStronglyMeasurable (fun ω => A ω x) μ)
    (ι : E →L[ℂ] F) (N : ℕ) (hN : 0 < N) (ρ C₀ M L b : ℝ)
    (hρ : 0 < ρ) (hρC₀ : ρ < C₀) (hM : 0 ≤ M) (hMC₀ : M ≤ C₀)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (hA : ∀ ω, ‖A ω‖ ≤ L)
    (hweak : ∀ ω x, ‖ι (A ω x)‖ ≤ M * ‖ι x‖)
    (hblock : ∀ word : List Ω, word.length = N → ∀ x,
      ‖listWord A word x‖ ≤ ρ ^ N * ‖x‖ + b * ‖ι x‖) :
    let C := ∑ r ∈ Finset.range N, (L / ρ) ^ r
    let D := b / (C₀ ^ N - ρ ^ N)
    0 ≤ C ∧ 0 ≤ D ∧ ∀ n x,
      ‖(pointwiseAnnealed μ A hmeas L hA ^ n) x‖ ≤
        C * ρ ^ n * ‖x‖ + D * C₀ ^ n * ‖ι x‖ := by
  obtain ⟨hC, hD, hword⟩ := TwoNormBlockIteration.uniform_twoNorm_bound
    (listWord A) ι (listWord_append A) N hN ρ C₀ M L b 1
    hρ hρC₀ hM hMC₀ hL hb zero_le_one
    (fun word _ x => strong_word_bound A L hL hA word x)
    (fun word x => by simpa using weak_word_bound A ι M hM hweak word x) hblock
  simp only [mul_one] at hD hword
  refine ⟨hC, hD, ?_⟩
  intro n x
  apply pointwiseAnnealed_pow_apply_bound μ A hmeas L hL hA n x
  intro word
  have h := hword (noiseWordList n word) x
  simpa only [listWord_noiseWordList, noiseWordList_length] using h

/-- A fixed-block local estimate with upper semicontinuous coefficients
produces one generator neighborhood and uniform actual annealed estimates
for every probability noise law supported there. The identified local
principal coefficient and its deterministic strict bound remain explicit;
the arbitrary-word and averaging conclusions are derived here. -/
theorem exists_robust_annealed_twoNorm_bound {G : Type*} [TopologicalSpace G]
    (T : G) (A : G → E →L[ℂ] E) (ι : E →L[ℂ] F)
    (N : ℕ) (hN : 0 < N) (ρ C₀ M L : ℝ)
    (hρ : 0 < ρ) (hρC₀ : ρ < C₀) (hM : 0 ≤ M) (hMC₀ : M ≤ C₀) (hL : 0 ≤ L)
    (U : Set G) (hU : IsOpen U) (hTU : T ∈ U)
    (hstrong : ∀ a ∈ U, ‖A a‖ ≤ L)
    (hweak : ∀ a ∈ U, ∀ x, ‖ι (A a x)‖ ≤ M * ‖ι x‖)
    (a b : (Fin N → G) → ℝ)
    (ha : UpperSemicontinuousAt a (fun _ => T))
    (hb : UpperSemicontinuousAt b (fun _ => T))
    (hstrict : a (fun _ => T) < ρ ^ N)
    (O : Set (Fin N → G)) (hO : O ∈ 𝓝 (fun _ => T))
    (hlocal : ∀ word ∈ O, ∀ x,
      ‖listWord A (List.ofFn word) x‖ ≤ a word * ‖x‖ + b word * ‖ι x‖) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ W ⊆ U ∧
      ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ζ : Ω → G), (∀ ω, ζ ω ∈ W) →
        (∀ x, AEStronglyMeasurable (fun ω => A (ζ ω) x) μ) →
        ∀ P : E →L[ℂ] E, (∀ x, P x = ∫ ω, A (ζ ω) x ∂μ) →
        ∀ n x, ‖(P ^ n) x‖ ≤ C * ρ ^ n * ‖x‖ + D * C₀ ^ n * ‖ι x‖ := by
  obtain ⟨W₀, hW₀, hTW₀, B, hB, hblock⟩ :=
    RobustTwoNormBlock.exists_robust_list_estimate N T (listWord A) ι a b ha hb
      ρ hstrict O hO hlocal
  let C := ∑ r ∈ Finset.range N, (L / ρ) ^ r
  let D := B / (C₀ ^ N - ρ ^ N)
  have hgap : 0 < C₀ ^ N - ρ ^ N :=
    sub_pos.mpr (pow_lt_pow_left₀ hρC₀ hρ.le hN.ne')
  refine ⟨W₀ ∩ U, hW₀.inter hU, ⟨hTW₀, hTU⟩, inter_subset_right,
    C, D, Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hL hρ.le) _),
    div_nonneg hB hgap.le, ?_⟩
  intro Ω _ μ _ ζ hζ hmeas P hP
  have hbound : ∀ ω, ‖A (ζ ω)‖ ≤ L := fun ω => hstrong _ (hζ ω).2
  have hblockζ : ∀ word : List Ω, word.length = N → ∀ x,
      ‖listWord (fun ω => A (ζ ω)) word x‖ ≤ ρ ^ N * ‖x‖ + B * ‖ι x‖ := by
    intro word hlen x
    rw [listWord_map]
    apply hblock (word.map ζ) (by simpa using hlen)
    intro z hz
    obtain ⟨ω, _hω, rfl⟩ := List.mem_map.mp hz
    exact (hζ ω).1
  have he : P = pointwiseAnnealed μ (fun ω => A (ζ ω)) hmeas L hbound := by
    ext x
    exact hP x
  obtain ⟨_hC, _hD, hpower⟩ := annealed_twoNorm_bound μ (fun ω => A (ζ ω)) hmeas
    ι N hN ρ C₀ M L B hρ hρC₀ hM hMC₀ hL hB hbound
    (fun ω x => hweak _ (hζ ω).2 x) hblockζ
  simpa only [he] using hpower

end LeanShared.FiniteBlockAnnealedEstimates
