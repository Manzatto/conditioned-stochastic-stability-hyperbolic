module

public import LeanShared.Dynamics.LocalProjectionPairHolder
public import LeanShared.Geometry.CompactPairChartSelection

/-! Finite local coordinate cocycles give Hölder projection fields without
assuming a global trivialization or a coherent chart itinerary. A common
chart for each nearby image pair is chosen from the actual compact cover;
all invariance and contraction identities remain local chart identities. -/
public noncomputable section
namespace LeanShared.FiniteAtlasProjectionHolder
open Set
open scoped NNReal

variable {X I R : Type*} [MetricSpace X] [CompactSpace X] [NormedRing R]

set_option maxHeartbeats 1800000 in
theorem bound (centers : Finset I) (patch : I → Set X)
    (cover : (univ : Set X) ⊆ ⋃ i ∈ centers, interior (patch i))
    (F G : X → X) (L : ℝ≥0) (forwardLip : LipschitzWith L F) (backwardLip : LipschitzWith L G)
    (P : I → X → R) (A AI D DI : I → I → X → R)
    (κ B C α : ℝ) (κnonnegative : 0 ≤ κ) (Bnonnegative : 0 ≤ B)
    (αnonnegative : 0 ≤ α) (small : 2 * κ ^ 2 < 1)
    (bunched : (2 * κ ^ 2) * (L : ℝ) ^ α < 1)
    (bounded : ∀ i ∈ centers, ∀ x ∈ patch i, ‖P i x‖ ≤ B ∧ ‖1 - P i x‖ ≤ B)
    (idempotent : ∀ i ∈ centers, ∀ x ∈ patch i, P i x * P i x = P i x)
    (forwardInverse : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      F x ∈ patch j → AI i j x * A i j x = 1)
    (backwardInverse : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      G x ∈ patch j → DI i j x * D i j x = 1)
    (forwardInvariant : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      F x ∈ patch j → P j (F x) * A i j x = A i j x * P i x)
    (backwardInvariant : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      G x ∈ patch j → (1 - P j (G x)) * D i j x = D i j x * (1 - P i x))
    (forwardStable : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      F x ∈ patch j → ‖A i j x * P i x‖ ≤ κ)
    (forwardUnstable : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      F x ∈ patch j → ‖AI i j x * (1 - P j (F x))‖ ≤ κ)
    (backwardStable : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      G x ∈ patch j → ‖D i j x * (1 - P i x)‖ ≤ κ)
    (backwardUnstable : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i,
      G x ∈ patch j → ‖DI i j x * P j (G x)‖ ≤ κ)
    (forwardHolder : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i, ∀ y ∈ patch i,
      F x ∈ patch j → F y ∈ patch j → dist x y < 1 →
        ‖A i j x - A i j y‖ ≤ C * dist x y ^ α)
    (backwardHolder : ∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ patch i, ∀ y ∈ patch i,
      G x ∈ patch j → G y ∈ patch j → dist x y < 1 →
        ‖D i j x - D i j y‖ ≤ C * dist x y ^ α) :
    ∃ H ≥ 0, ∀ i ∈ centers, ∀ x ∈ patch i, ∀ y ∈ patch i,
      ‖P i x - P i y‖ ≤ H * dist x y ^ α := by
  obtain ⟨r₀, positiveR₀, common⟩ := CompactPairChartSelection.exists_radius
    (univ : Set X) isCompact_univ centers patch cover
  let r := min 1 (r₀ / ((L : ℝ) + 1))
  have positiveR : 0 < r := lt_min zero_lt_one (div_pos positiveR₀ (by positivity))
  have imageNear (u : X → X) (lip : LipschitzWith L u) (x y : X) (near : dist x y < r) :
      dist (u x) (u y) < r₀ := by
    have smallDist : dist x y < r₀ / ((L : ℝ) + 1) := near.trans_le (min_le_right _ _)
    have scaled : dist x y * ((L : ℝ) + 1) < r₀ :=
      (lt_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mp smallDist
    have lipschitz := lip.dist_le_mul x y
    nlinarith [dist_nonneg (x := x) (y := y)]
  let State := {s : I × X × X // s.1 ∈ centers ∧ s.2.1 ∈ patch s.1 ∧ s.2.2 ∈ patch s.1}
  have next (u : X → X) (lip : LipschitzWith L u) (s : State) :
      ∃ z : State, dist s.val.2.1 s.val.2.2 < r →
        z.val.2.1 = u s.val.2.1 ∧ z.val.2.2 = u s.val.2.2 := by
    by_cases near : dist s.val.2.1 s.val.2.2 < r
    · obtain ⟨j, selected, first, other⟩ := common (u s.val.2.1) (mem_univ _)
        (u s.val.2.2) (imageNear u lip _ _ near)
      exact ⟨⟨(j, u s.val.2.1, u s.val.2.2), selected, first, other⟩, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨s, fun h => (near h).elim⟩
  choose f hf using next F forwardLip
  choose g hg using next G backwardLip
  let p : State → R := fun s => P s.val.1 s.val.2.1
  let q : State → R := fun s => P s.val.1 s.val.2.2
  have fmem (s : State) (near : dist s.val.2.1 s.val.2.2 < r) :
      F s.val.2.1 ∈ patch (f s).val.1 ∧ F s.val.2.2 ∈ patch (f s).val.1 := by
    rw [← (hf s near).1, ← (hf s near).2]
    exact ⟨(f s).property.2.1, (f s).property.2.2⟩
  have gmem (s : State) (near : dist s.val.2.1 s.val.2.2 < r) :
      G s.val.2.1 ∈ patch (g s).val.1 ∧ G s.val.2.2 ∈ patch (g s).val.1 := by
    rw [← (hg s near).1, ← (hg s near).2]
    exact ⟨(g s).property.2.1, (g s).property.2.2⟩
  obtain ⟨H, nonnegativeH, estimate⟩ := HyperbolicProjectionPerturbation.local_pair_holder
    (fun s : State => dist s.val.2.1 s.val.2.2) f g p q
    (fun s => A s.val.1 (f s).val.1 s.val.2.1)
    (fun s => AI s.val.1 (f s).val.1 s.val.2.1)
    (fun s => A s.val.1 (f s).val.1 s.val.2.2)
    (fun s => D s.val.1 (g s).val.1 s.val.2.1)
    (fun s => DI s.val.1 (g s).val.1 s.val.2.1)
    (fun s => D s.val.1 (g s).val.1 s.val.2.2)
    κ B C L α r κnonnegative Bnonnegative L.coe_nonneg αnonnegative positiveR small bunched
    (fun _ => dist_nonneg)
    (fun s => ⟨(bounded _ s.property.1 _ s.property.2.1).1,
      (bounded _ s.property.1 _ s.property.2.2).1,
      (bounded _ s.property.1 _ s.property.2.2).2⟩)
    (fun s => idempotent _ s.property.1 _ s.property.2.1)
    (fun s => idempotent _ s.property.1 _ s.property.2.2)
    (fun s near => by rw [(hf s near).1, (hf s near).2]; exact forwardLip.dist_le_mul _ _)
    (fun s near => by rw [(hg s near).1, (hg s near).2]; exact backwardLip.dist_le_mul _ _)
    (fun s near => forwardInverse _ s.property.1 _ (f s).property.1 _ s.property.2.1 (fmem s near).1)
    (fun s near => backwardInverse _ s.property.1 _ (g s).property.1 _ s.property.2.1 (gmem s near).1)
    (fun s near => by
      dsimp only [p]; rw [(hf s near).1]
      exact forwardInvariant _ s.property.1 _ (f s).property.1 _ s.property.2.1 (fmem s near).1)
    (fun s near => by
      dsimp only [q]; rw [(hf s near).2]
      exact forwardInvariant _ s.property.1 _ (f s).property.1 _ s.property.2.2 (fmem s near).2)
    (fun s near => by
      dsimp only [p]; rw [(hg s near).1]
      exact backwardInvariant _ s.property.1 _ (g s).property.1 _ s.property.2.1 (gmem s near).1)
    (fun s near => by
      dsimp only [q]; rw [(hg s near).2]
      exact backwardInvariant _ s.property.1 _ (g s).property.1 _ s.property.2.2 (gmem s near).2)
    (fun s near => forwardStable _ s.property.1 _ (f s).property.1 _ s.property.2.2 (fmem s near).2)
    (fun s near => by
      dsimp only [p]; rw [(hf s near).1]
      exact forwardUnstable _ s.property.1 _ (f s).property.1 _ s.property.2.1 (fmem s near).1)
    (fun s near => backwardStable _ s.property.1 _ (g s).property.1 _ s.property.2.2 (gmem s near).2)
    (fun s near => by
      dsimp only [p]; rw [(hg s near).1]
      exact backwardUnstable _ s.property.1 _ (g s).property.1 _ s.property.2.1 (gmem s near).1)
    (fun s near => forwardHolder _ s.property.1 _ (f s).property.1 _ s.property.2.1 _
      s.property.2.2 (fmem s near).1 (fmem s near).2 (near.trans_le (min_le_left _ _)))
    (fun s near => backwardHolder _ s.property.1 _ (g s).property.1 _ s.property.2.1 _
      s.property.2.2 (gmem s near).1 (gmem s near).2 (near.trans_le (min_le_left _ _)))
  exact ⟨H, nonnegativeH, fun i hi x hx y hy => estimate ⟨(i, x, y), hi, hx, hy⟩⟩

end LeanShared.FiniteAtlasProjectionHolder
