module
public import LeanShared.Analysis.ParameterizedContraction
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The actual Lyapunov--Perron transformation for backward orbits of a small
nonlinear perturbation of a hyperbolic split map. The inverse expanding block
and the contracting block both have bound `k`; the nonlinear part has bound
`δ`. The transformation on bounded sequences has contraction constant `k + δ`.
No graph transform, invariant graph, or backward orbit is supplied as data. -/
public noncomputable section
namespace LeanShared.HyperbolicBackwardTransform
open scoped NNReal BoundedContinuousFunction

@[expose] def raw {U S : Type*} [NormedAddCommGroup U] [NormedAddCommGroup S]
    (A : ℕ → U → U) (B : ℕ → S → S) (N : ℕ → U × S → U × S)
    (u : U) (z : ℕ → U × S) : ℕ → U × S
  | 0 => (u, B 0 (z 1).2 + (N 0 (z 1)).2)
  | n + 1 => (A n ((z n).1 - (N n (z (n + 1))).1),
      B (n + 1) (z (n + 2)).2 + (N (n + 1) (z (n + 2))).2)

theorem raw_distance {U S : Type*} [NormedAddCommGroup U] [NormedAddCommGroup S]
    (A : ℕ → U → U) (B : ℕ → S → S) (N : ℕ → U × S → U × S)
    (k δ : ℝ≥0) (hk : k ≤ 1)
    (hA : ∀ n, LipschitzWith k (A n)) (hB : ∀ n, LipschitzWith k (B n))
    (hN : ∀ n, LipschitzWith δ (N n)) (u : U)
    (z w : ℕ → U × S) (D : ℝ) (distance : ∀ n, dist (z n) (w n) ≤ D) (n : ℕ) :
    dist (raw A B N u z n) (raw A B N u w n) ≤ (k + δ : ℝ≥0) * D := by
  have fst (m : ℕ) : dist (z m).1 (w m).1 ≤ D :=
    (le_max_left _ _).trans (distance m)
  have snd (m : ℕ) : dist (z m).2 (w m).2 ≤ D :=
    (le_max_right _ _).trans (distance m)
  have nfst (m i : ℕ) : dist (N i (z m)).1 (N i (w m)).1 ≤ (δ : ℝ) * D :=
    (le_max_left _ _).trans (((hN i).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (distance m) δ.coe_nonneg))
  have nsnd (m i : ℕ) : dist (N i (z m)).2 (N i (w m)).2 ≤ (δ : ℝ) * D :=
    (le_max_right _ _).trans (((hN i).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (distance m) δ.coe_nonneg))
  have stable (m i : ℕ) : dist (B i (z m).2 + (N i (z m)).2)
      (B i (w m).2 + (N i (w m)).2) ≤ (k + δ : ℝ≥0) * D := by
    calc
      _ ≤ dist (B i (z m).2) (B i (w m).2) + dist (N i (z m)).2 (N i (w m)).2 :=
        dist_add_add_le _ _ _ _
      _ ≤ (k : ℝ) * D + δ * D := add_le_add
        (((hB i).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (snd m) k.coe_nonneg))
        (nsnd m i)
      _ = _ := by rw [NNReal.coe_add, add_mul]
  cases n with
  | zero => simpa only [raw, dist_prod_same_left] using stable 1 0
  | succ n =>
    rw [raw, raw, Prod.dist_eq]
    apply max_le _ (stable (n + 2) (n + 1))
    calc
      _ ≤ k * dist ((z n).1 - (N n (z (n + 1))).1)
          ((w n).1 - (N n (w (n + 1))).1) := (hA n).dist_le_mul _ _
      _ ≤ k * (dist (z n).1 (w n).1 +
          dist (N n (z (n + 1))).1 (N n (w (n + 1))).1) :=
        mul_le_mul_of_nonneg_left (dist_sub_sub_le _ _ _ _) k.coe_nonneg
      _ ≤ (k : ℝ) * (D + δ * D) :=
        mul_le_mul_of_nonneg_left (add_le_add (fst n) (nfst (n + 1) n)) k.coe_nonneg
      _ ≤ (k + δ : ℝ≥0) * D := by
        have hD : 0 ≤ D := (dist_nonneg (x := z 0) (y := w 0)).trans (distance 0)
        have hk' : (k : ℝ) ≤ 1 := hk
        rw [NNReal.coe_add]
        nlinarith [mul_nonneg δ.coe_nonneg hD]

theorem raw_zero_bound {U S : Type*} [NormedAddCommGroup U] [NormedAddCommGroup S]
    (A : ℕ → U → U) (B : ℕ → S → S) (N : ℕ → U × S → U × S)
    (k : ℝ≥0) (hA : ∀ n, LipschitzWith k (A n))
    (zeroA : ∀ n, A n 0 = 0) (zeroB : ∀ n, B n 0 = 0)
    (C : ℝ) (bound : ∀ n, ‖N n 0‖ ≤ C) (u : U) (n : ℕ) :
    ‖raw A B N u (fun _ => 0) n‖ ≤ max ‖u‖ (((k : ℝ) + 1) * C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (bound 0)
  have fst (i : ℕ) : ‖(N i 0).1‖ ≤ C := (le_max_left _ _).trans (bound i)
  have snd (i : ℕ) : ‖(N i 0).2‖ ≤ C := (le_max_right _ _).trans (bound i)
  have stable (i : ℕ) : ‖B i 0 + (N i 0).2‖ ≤ ((k : ℝ) + 1) * C := by
    rw [zeroB, zero_add]
    exact (snd i).trans (by nlinarith [mul_nonneg k.coe_nonneg hC])
  cases n with
  | zero => exact max_le (le_max_left _ _) ((stable 0).trans (le_max_right _ _))
  | succ n =>
    apply max_le _ ((stable (n + 1)).trans (le_max_right _ _))
    apply le_trans _ (le_max_right _ _)
    calc
      ‖A n (0 - (N n 0).1)‖ ≤ k * ‖0 - (N n 0).1‖ := by
        simpa only [zeroA, dist_zero_right] using (hA n).dist_le_mul (0 - (N n 0).1) 0
      _ = k * ‖(N n 0).1‖ := by rw [zero_sub, norm_neg]
      _ ≤ (k : ℝ) * C := mul_le_mul_of_nonneg_left (fst n) k.coe_nonneg
      _ ≤ ((k : ℝ) + 1) * C := by nlinarith

@[expose] def transform {U S : Type*} [NormedAddCommGroup U] [NormedAddCommGroup S]
    (A : ℕ → U → U) (B : ℕ → S → S) (N : ℕ → U × S → U × S)
    (k δ : ℝ≥0) (hk : k ≤ 1)
    (hA : ∀ n, LipschitzWith k (A n)) (hB : ∀ n, LipschitzWith k (B n))
    (hN : ∀ n, LipschitzWith δ (N n))
    (zeroA : ∀ n, A n 0 = 0) (zeroB : ∀ n, B n 0 = 0)
    (C : ℝ) (bound : ∀ n, ‖N n 0‖ ≤ C) (u : U) (z : ℕ →ᵇ U × S) : ℕ →ᵇ U × S :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (raw A B N u z)
    ((k + δ : ℝ≥0) * ‖z‖ + max ‖u‖ (((k : ℝ) + 1) * C)) fun n => by
      calc
        _ ≤ dist (raw A B N u z n) (raw A B N u (fun _ => 0) n) +
            ‖raw A B N u (fun _ => 0) n‖ := by
          simpa only [dist_zero_right] using
            dist_triangle (raw A B N u z n) (raw A B N u (fun _ => 0) n) 0
        _ ≤ _ := add_le_add
          (raw_distance A B N k δ hk hA hB hN u z (fun _ => 0) ‖z‖
            (fun i => by simpa only [dist_zero_right] using z.norm_coe_le_norm i) n)
          (raw_zero_bound A B N k hA zeroA zeroB C bound u n)

theorem transform_lipschitz {U S : Type*} [NormedAddCommGroup U] [NormedAddCommGroup S]
    (A : ℕ → U → U) (B : ℕ → S → S) (N : ℕ → U × S → U × S)
    (k δ : ℝ≥0) (hk : k ≤ 1)
    (hA : ∀ n, LipschitzWith k (A n)) (hB : ∀ n, LipschitzWith k (B n))
    (hN : ∀ n, LipschitzWith δ (N n))
    (zeroA : ∀ n, A n 0 = 0) (zeroB : ∀ n, B n 0 = 0)
    (C : ℝ) (bound : ∀ n, ‖N n 0‖ ≤ C) (u : U) :
    LipschitzWith (k + δ) (transform A B N k δ hk hA hB hN zeroA zeroB C bound u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (BoundedContinuousFunction.dist_le
    (mul_nonneg (k + δ).coe_nonneg dist_nonneg)).mpr
  intro n
  exact raw_distance A B N k δ hk hA hB hN u z w (dist z w)
    (fun i => BoundedContinuousFunction.dist_coe_le_dist i) n

end LeanShared.HyperbolicBackwardTransform
