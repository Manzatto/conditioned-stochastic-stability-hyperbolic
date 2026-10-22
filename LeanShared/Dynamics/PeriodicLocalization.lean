module
public import LeanShared.Dynamics.PseudoOrbitNearCore
public import LeanShared.Dynamics.BasicHyperbolicPeriodicShadowing
public import LeanShared.Dynamics.HyperbolicExpansivity

/-! Localization of almost periodic orbit segments. An orbit segment of length `n` in the
closed isolating neighborhood that nearly closes up is uniformly shadowed, at all times
`0 ≤ l ≤ n`, by a genuine `n`-periodic point of the basic set (near-core compactness,
projection to `Λ` and periodic shadowing). Two `n`-periodic points of `Λ` that stay within
the expansivity radius at all times coincide. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter Metric IsManifold Bundle
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.periodic_closing_shadow (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (δloc : ℝ) (hδ : 0 < δloc) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ n : ℕ, 0 < n → ∀ x : M,
      (∀ l < n, (T : M → M)^[l] x ∈ closure V) → dist ((T : M → M)^[n] x) x < ε1 →
      ∃ p ∈ Λ, (T : M → M)^[n] p = p ∧
        ∀ l ≤ n, dist ((T : M → M)^[l] x) ((T : M → M)^[l] p) < δloc := by
  obtain ⟨η, hη, shadow⟩ := b.periodic_shadowing forward inverse (δloc / 2) (by positivity)
  have uniform := CompactSpace.uniformContinuous_of_continuous T.continuous
  rw [Metric.uniformContinuous_iff] at uniform
  obtain ⟨η1, hη1, hT⟩ := uniform (η / 3) (by positivity)
  set η' := min (min η1 (η / 3)) (δloc / 4)
  have hη' : 0 < η' := lt_min (lt_min hη1 (by positivity)) (by positivity)
  obtain ⟨δnc, hδnc, near⟩ := PseudoOrbitNearCore.near_core T (closure V) isClosed_closure η' hη'
  set ε1 := min δnc (min (η / 3) (δloc / 4))
  refine ⟨ε1, lt_min hδnc (lt_min (by positivity) (by positivity)), fun n hn x hx hclose => ?_⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  set u : ℤ → M := fun l => (T : M → M)^[(l % n).toNat] x
  have uInside (l : ℤ) : u l ∈ closure V := by
    have := Int.emod_nonneg l hn'.ne'
    have := Int.emod_lt_of_pos l hn'
    exact hx _ (by omega)
  have uStep (l : ℤ) : dist (T (u l)) (u (l + 1)) < ε1 := by
    have r0 := Int.emod_nonneg l hn'.ne'
    have r1 := Int.emod_lt_of_pos l hn'
    have decomposition := Int.emod_add_mul_ediv l n
    rcases lt_or_eq_of_le (show l % n + 1 ≤ n by omega) with lt | eq
    · have next : (l + 1) % n = l % n + 1 := by
        rw [show l + 1 = (l % n + 1) + n * (l / n) by omega, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) lt]
      have same : T (u l) = u (l + 1) := by
        simp only [u, next, show (l % n + 1).toNat = (l % n).toNat + 1 by omega,
          Function.iterate_succ_apply']
      rw [same, dist_self]
      exact lt_min hδnc (lt_min (by positivity) (by positivity))
    · have next : (l + 1) % n = 0 := by
        rw [show l + 1 = n * (l / n + 1) by rw [mul_add, mul_one]; omega]
        exact Int.mul_emod_right _ _
      have wrap : T (u l) = (T : M → M)^[n] x := by
        simp only [u]
        rw [← Function.iterate_succ_apply' (T : M → M), show (l % n).toNat.succ = n by omega]
      rw [wrap]
      simp only [u, next, Int.toNat_zero, Function.iterate_zero, id]
      exact hclose
  have nearCore (l : ℤ) : infDist (u l) Λ < η' := by
    have := near (fun k => u (-k)) (fun k => uInside _) (fun k => by
      have := uStep (-(k + 1))
      rw [show -(k + 1) + 1 = -k by ring] at this
      exact this.trans_le (min_le_left _ _)) (-l)
    rw [neg_neg, ← b.isolated] at this
    exact this
  have chooseZ (l : ℤ) : ∃ z ∈ Λ, dist (u l) z < η' :=
    (infDist_lt_iff b.nonempty).mp (nearCore l)
  choose zf zfΛ zfClose using chooseZ
  set z : ℤ → M := fun l => zf (l % n)
  have uPeriodic (l : ℤ) : u (l % n) = u l := by
    simp only [u, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have zClose (l : ℤ) : dist (u l) (z l) < η' := by
    have := zfClose (l % n)
    rwa [uPeriodic] at this
  let reference : ℤ → Λ := fun k => ⟨z (-k), zfΛ _⟩
  have periodicRef (k : ℤ) : reference (k + (n : ℤ)) = reference k := by
    apply Subtype.ext
    simp only [reference, z, show -(k + (n : ℤ)) = -k + (n : ℤ) * (-1) by ring,
      Int.add_mul_emod_self_left]
  have stepRef (k : ℤ) : dist (T (reference (k + 1)).val) (reference k).val < η := by
    simp only [reference]
    have l1 : -(k + 1) + 1 = -k := by ring
    have a1 : dist (T (z (-(k + 1)))) (T (u (-(k + 1)))) < η / 3 :=
      hT (by rw [dist_comm]; exact (zClose _).trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    have a2 : dist (T (u (-(k + 1)))) (u (-k)) < η / 3 := by
      have := uStep (-(k + 1))
      rw [l1] at this
      exact this.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have a3 : dist (u (-k)) (z (-k)) < η / 3 :=
      (zClose _).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    calc dist (T (z (-(k + 1)))) (z (-k)) ≤
        dist (T (z (-(k + 1)))) (T (u (-(k + 1)))) + dist (T (u (-(k + 1)))) (u (-k)) +
          dist (u (-k)) (z (-k)) := dist_triangle4 _ _ _ _
      _ < η / 3 + η / 3 + η / 3 := by linarith
      _ = η := by ring
  obtain ⟨p, pΛ, fixed, close⟩ := shadow n reference periodicRef stepRef
  refine ⟨p, pΛ, fixed, fun l hl => ?_⟩
  have hp (l : ℕ) : dist ((T : M → M)^[l] p) (z l) < δloc / 2 := by
    have := close (-(l : ℤ))
    rw [BilateralHomeomorphismOrbit.neg_nat_time] at this
    simpa only [reference, neg_neg] using this
  rcases lt_or_eq_of_le hl with lt | eq
  · have ul : u l = (T : M → M)^[l] x := by
      simp only [u]
      rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast lt), Int.toNat_natCast]
    have h1 := zClose (l : ℤ)
    rw [ul] at h1
    have h2 := hp l
    have : η' ≤ δloc / 4 := min_le_right _ _
    calc dist ((T : M → M)^[l] x) ((T : M → M)^[l] p) ≤
        dist ((T : M → M)^[l] x) (z l) + dist (z l) ((T : M → M)^[l] p) := dist_triangle _ _ _
      _ < δloc / 4 + δloc / 2 := by rw [dist_comm (z l)]; linarith
      _ < δloc := by linarith
  · rw [eq, fixed]
    have h0 : u 0 = x := by simp only [u, Int.zero_emod, Int.toNat_zero, Function.iterate_zero, id]
    have h1 := zClose 0
    rw [h0] at h1
    have h2 := hp 0
    simp only [Function.iterate_zero, id, Nat.cast_zero] at h2
    have h3 : dist ((T : M → M)^[n] x) x < δloc / 4 := hclose.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    have : η' ≤ δloc / 4 := min_le_right _ _
    calc dist ((T : M → M)^[n] x) p ≤ dist ((T : M → M)^[n] x) x + dist x (z 0) + dist (z 0) p :=
          dist_triangle4 _ _ _ _
      _ < δloc / 4 + δloc / 4 + δloc / 2 := by rw [dist_comm (z 0)]; linarith
      _ = δloc := by ring

theorem iterate_periodic_mod (f : M → M) (n : ℕ) (x : M) (fixed : f^[n] x = x) (j : ℕ) :
    f^[j] x = f^[j % n] x := by
  conv_lhs => rw [← Nat.mod_add_div j n, Function.iterate_add_apply]
  rw [Function.iterate_mul, Function.iterate_fixed fixed]

theorem symm_iterate_periodic (n : ℕ) (hn : 0 < n) (x : M) (fixed : (T : M → M)^[n] x = x)
    (j : ℕ) : (T.symm : M → M)^[j] x = (T : M → M)^[(n - 1) * j] x := by
  have total : (T : M → M)^[j] ((T : M → M)^[(n - 1) * j] x) = x := by
    have hle : j ≤ n * j := Nat.le_mul_of_pos_left j hn
    rw [← Function.iterate_add_apply, Nat.sub_mul, one_mul, Nat.add_sub_cancel' hle,
      Function.iterate_mul, Function.iterate_fixed fixed]
  have inverse : Function.LeftInverse ((T.symm : M → M)^[j]) ((T : M → M)^[j]) :=
    Function.LeftInverse.iterate T.symm_apply_apply j
  calc (T.symm : M → M)^[j] x = (T.symm : M → M)^[j] ((T : M → M)^[j]
        ((T : M → M)^[(n - 1) * j] x)) := by rw [total]
    _ = (T : M → M)^[(n - 1) * j] x := inverse _

theorem BasicData.periodic_unique (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ δdis : ℝ, 0 < δdis ∧ ∀ n : ℕ, 0 < n → ∀ p ∈ Λ, ∀ q ∈ Λ,
      (T : M → M)^[n] p = p → (T : M → M)^[n] q = q →
      (∀ l < n, dist ((T : M → M)^[l] p) ((T : M → M)^[l] q) ≤ δdis) → p = q := by
  obtain ⟨c, hc, expansive⟩ := b.exists_expansivity_radius forward inverse
  refine ⟨c, hc, fun n hn p hp q hq fp fq close => expansive p hp q hq fun j => ⟨?_, ?_⟩⟩
  · rw [iterate_periodic_mod _ n p fp, iterate_periodic_mod _ n q fq]
    exact close _ (Nat.mod_lt _ hn)
  · rw [symm_iterate_periodic n hn p fp, symm_iterate_periodic n hn q fq,
      iterate_periodic_mod _ n p fp, iterate_periodic_mod _ n q fq]
    exact close _ (Nat.mod_lt _ hn)

end LeanShared.HyperbolicBasicSet
