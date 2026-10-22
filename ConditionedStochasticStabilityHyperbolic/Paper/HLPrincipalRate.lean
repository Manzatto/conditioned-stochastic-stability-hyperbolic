module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPrincipalContraction

/-! The strict deterministic hyperbolicity rate is derived from HL and the
actual exponent pair. This does not assert an ambient survivor-pressure bound;
that further classical comparison must include shadowing/distortion controls. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

def principalRate (t s : ℝ) : ℝ :=
  max (h.basic.hyperbolic.contraction ^ t) (h.basic.hyperbolic.contraction ^ (-s))

theorem principalRate_pos (t s : ℝ) : 0 < h.principalRate t s :=
  lt_max_of_lt_left (Real.rpow_pos_of_pos h.basic.hyperbolic.contraction_pos t)

theorem principalRate_lt_one {t s : ℝ} (ht : 0 < t) (hs : s < 0) :
    h.principalRate t s < 1 :=
  max_lt (Real.rpow_lt_one h.basic.hyperbolic.contraction_pos.le
    h.basic.hyperbolic.contraction_lt_one ht)
    (Real.rpow_lt_one h.basic.hyperbolic.contraction_pos.le
      h.basic.hyperbolic.contraction_lt_one (neg_pos.mpr hs))

/-- Both literal deterministic factors yield one strict exponential rate;
the only prefactor is the actual HL hyperbolicity constant at the exponents. -/
theorem principal_max_bound {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 0)
    (N : ℕ) (x : M) (hx : x ∈ Λ) :
    max
      ((IntrinsicPrincipalDensity.stableFactor (fun _ : Unit => (T : M → M))
        (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
        (List.replicate N ()) x (h.basic.hyperbolic.stable
          (IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) (List.replicate N ()) x))) ^ t)
      ((IntrinsicPrincipalDensity.inverseFactor (fun _ : Unit => (T : M → M))
        (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
        (List.replicate N ()) x (h.basic.hyperbolic.unstable x)) ^ (-s)) ≤
      max (h.basic.hyperbolic.constant ^ t) (h.basic.hyperbolic.constant ^ (-s)) *
        h.principalRate t s ^ N := by
  have stableNonneg : 0 ≤ IntrinsicPrincipalDensity.stableFactor
      (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
      (fun _ => h.differential) (List.replicate N ()) x
      (h.basic.hyperbolic.stable (IntrinsicPrincipalDensity.orbit
        (fun _ : Unit => (T : M → M)) (List.replicate N ()) x)) := by
    unfold IntrinsicPrincipalDensity.stableFactor
    exact ContinuousLinearMap.opNorm_nonneg _
  have unstableNonneg : 0 ≤ IntrinsicPrincipalDensity.inverseFactor
      (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
      (fun _ => h.differential) (List.replicate N ()) x (h.basic.hyperbolic.unstable x) := by
    unfold IntrinsicPrincipalDensity.inverseFactor
    exact ContinuousLinearMap.opNorm_nonneg _
  have stable := Real.rpow_le_rpow stableNonneg (h.principal_stableFactor_bound N x hx) ht
  have unstable := Real.rpow_le_rpow unstableNonneg (h.principal_inverseFactor_bound N x hx)
    (neg_nonneg.mpr hs)
  have expansion (a : ℝ) :
      (h.basic.hyperbolic.constant * h.basic.hyperbolic.contraction ^ N) ^ a =
      h.basic.hyperbolic.constant ^ a * (h.basic.hyperbolic.contraction ^ a) ^ N := by
    rw [Real.mul_rpow h.basic.hyperbolic.constant_pos.le
      (pow_nonneg h.basic.hyperbolic.contraction_pos.le N),
      ← Real.rpow_pow_comm h.basic.hyperbolic.contraction_pos.le]
  rw [expansion] at stable unstable
  have hχt := Real.rpow_nonneg h.basic.hyperbolic.contraction_pos.le t
  have hχs := Real.rpow_nonneg h.basic.hyperbolic.contraction_pos.le (-s)
  have hCt := Real.rpow_nonneg h.basic.hyperbolic.constant_pos.le t
  dsimp only [principalRate]
  apply max_le
  · exact stable.trans (mul_le_mul
      (le_max_left _ _) (pow_le_pow_left₀ hχt (le_max_left _ _) N)
      (pow_nonneg hχt N) (hCt.trans (le_max_left _ _)))
  · exact unstable.trans (mul_le_mul
      (le_max_right _ _) (pow_le_pow_left₀ hχs (le_max_right _ _) N)
      (pow_nonneg hχs N) (hCt.trans (le_max_left _ _)))

end ConditionedStochasticStabilityHyperbolic.Paper.HL
