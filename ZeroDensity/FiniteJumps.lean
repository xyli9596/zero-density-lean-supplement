import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ZeroDensity.FiniteJumps
open Set

noncomputable def density (s : Finset ℝ) (w : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∑ η ∈ s, if η ≤ θ then w η else 0

theorem density_monotone (s : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ η ∈ s, 0 ≤ w η) :
    Monotone (density s w) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro η hη
  by_cases ha : η ≤ a
  · simp [ha, ha.trans hab]
  · by_cases hb : η ≤ b
    · simpa [ha, hb] using hw η hη
    · simp [ha, hb]

theorem density_eq_of_no_jumps (s : Finset ℝ) (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (h : ∀ η ∈ s, η ∉ Icc a b) : density s w a = density s w b := by
  apply Finset.sum_congr rfl
  intro η hη
  have he : (η ≤ a) ↔ (η ≤ b) := by
    constructor
    · exact fun ha => ha.trans hab
    · intro hb
      have : ¬ a ≤ η := fun ha => h η hη ⟨ha, hb⟩
      exact (lt_of_not_ge this).le
  simp only [he]

/-- A compact interval disjoint from a finite jump set admits a positive buffer. -/
theorem finite_buffer (s : Finset ℝ) {a b : ℝ} (_hab : a ≤ b)
    (h : ∀ η ∈ s, η ∉ Icc a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η ∈ s, η ∉ Icc (a - δ) (b + δ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert c s hc ih =>
    have hs : ∀ η ∈ s, η ∉ Icc a b := fun η hη => h η (Finset.mem_insert_of_mem hη)
    obtain ⟨δ, hδ, hd⟩ := ih hs
    have hcb : c < a ∨ b < c := by
      have hn := h c (Finset.mem_insert_self c s)
      simpa only [mem_Icc, not_and_or, not_le] using hn
    rcases hcb with hca | hbc
    · let ε := min δ ((a - c) / 2)
      have hε : 0 < ε := lt_min hδ (by linarith)
      refine ⟨ε, hε, ?_⟩
      intro η hη hn
      rcases Finset.mem_insert.mp hη with rfl | hη
      · have hmin := min_le_right δ ((a - η) / 2)
        have hlo := hn.1
        dsimp [ε] at hlo
        linarith
      · apply hd η hη
        have heδ : ε ≤ δ := min_le_left _ _
        exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
    · let ε := min δ ((c - b) / 2)
      have hε : 0 < ε := lt_min hδ (by linarith)
      refine ⟨ε, hε, ?_⟩
      intro η hη hn
      rcases Finset.mem_insert.mp hη with rfl | hη
      · have hmin := min_le_right δ ((η - b) / 2)
        have hhi := hn.2
        dsimp [ε] at hhi
        linarith
      · apply hd η hη
        have heδ : ε ≤ δ := min_le_left _ _
        exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

/-- Density is constant throughout a closed interval containing no jumps. -/
theorem density_constant_on_Icc (s : Finset ℝ) (w : ℝ → ℝ) {a b : ℝ}
    (_hab : a ≤ b) (h : ∀ η ∈ s, η ∉ Icc a b) {t : ℝ} (ht : t ∈ Icc a b) :
    density s w t = density s w a := by
  symm
  apply density_eq_of_no_jumps s w ht.1
  intro η hη hηt
  exact h η hη ⟨hηt.1, hηt.2.trans ht.2⟩

/-- A jump-free interval can be enlarged without changing its density. -/
theorem buffered_density (s : Finset ℝ) (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (h : ∀ η ∈ s, η ∉ Icc a b) :
    ∃ δ : ℝ, 0 < δ ∧ density s w (a - δ) = density s w a ∧
      density s w (b + δ) = density s w b := by
  obtain ⟨δ, hδ, hd⟩ := finite_buffer s hab h
  refine ⟨δ, hδ, ?_, ?_⟩
  · apply density_eq_of_no_jumps s w (by linarith)
    intro η hη he
    exact hd η hη ⟨he.1, by linarith [he.2]⟩
  · symm
    apply density_eq_of_no_jumps s w (by linarith)
    intro η hη he
    exact hd η hη ⟨by linarith [he.1], he.2⟩

/-- Away from the finite jump set the step density is locally constant. -/
theorem density_locally_constant (s : Finset ℝ) (w : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∉ s) : ∀ᶠ t in nhds θ, density s w t = density s w θ := by
  have hn : ∀ η ∈ s, η ∉ Icc θ θ := by
    intro η hη he
    have heq : η = θ := le_antisymm he.2 he.1
    exact hθ (heq ▸ hη)
  obtain ⟨δ, hδ, hd⟩ := finite_buffer s le_rfl hn
  have hm : Ioo (θ - δ) (θ + δ) ∈ nhds θ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  filter_upwards [hm] with t ht
  apply Finset.sum_congr rfl
  intro η hη
  have ho : η < θ - δ ∨ θ + δ < η := by
    simpa only [mem_Icc, not_and_or, not_le] using hd η hη
  rcases ho with hlo | hhi
  · have hηt : η ≤ t := (hlo.trans ht.1).le
    have hηθ : η ≤ θ := by linarith
    simp [hηt, hηθ]
  · have hηt : ¬ η ≤ t := by linarith [ht.2]
    have hηθ : ¬ η ≤ θ := by linarith
    simp [hηt, hηθ]

/-- Nonnegative weights are unnecessary for continuity away from jumps. -/
theorem density_continuousAt (s : Finset ℝ) (w : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∉ s) : ContinuousAt (density s w) θ := by
  exact continuousAt_const.congr_of_eventuallyEq (density_locally_constant s w hθ)

/-- Zero-weight positions are not actual jumps. -/
noncomputable def activeJumps (s : Finset ℝ) (w : ℝ → ℝ) : Finset ℝ :=
  s.filter (fun η => w η ≠ 0)

@[simp] theorem mem_activeJumps (s : Finset ℝ) (w : ℝ → ℝ) (η : ℝ) :
    η ∈ activeJumps s w ↔ η ∈ s ∧ w η ≠ 0 := by
  classical
  simp [activeJumps]

/-- Removing zero-weight positions leaves the density unchanged. -/
@[simp] theorem density_activeJumps (s : Finset ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    density (activeJumps s w) w θ = density s w θ := by
  classical
  unfold density activeJumps
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro η hη
  by_cases hw : w η = 0
  · simp [hw]
  · simp [hw]

/-- Buffering requires avoidance only of positions with nonzero weight. -/
theorem buffered_density_activeJumps (s : Finset ℝ) (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (h : ∀ η ∈ activeJumps s w, η ∉ Icc a b) :
    ∃ δ : ℝ, 0 < δ ∧ density s w (a - δ) = density s w a ∧
      density s w (b + δ) = density s w b := by
  simpa only [density_activeJumps] using buffered_density (activeJumps s w) w hab h

/-- The convention including the jump at θ makes the density right-continuous. -/
theorem density_continuousWithinAt_right (s : Finset ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    ContinuousWithinAt (density s w) (Ici θ) θ := by
  have hall : ∀ᶠ t in nhdsWithin θ (Ici θ), ∀ η ∈ s, (η ≤ t ↔ η ≤ θ) := by
    rw [Filter.eventually_all_finset]
    intro η hη
    by_cases hle : η ≤ θ
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨fun _ => hle, fun _ => hle.trans ht⟩
    · have hm : Iio η ∈ nhds θ := isOpen_Iio.mem_nhds (lt_of_not_ge hle)
      filter_upwards [nhdsWithin_le_nhds hm] with t ht
      exact iff_of_false (not_le_of_gt ht) hle
  have he : (density s w) =ᶠ[nhdsWithin θ (Ici θ)] (fun _ => density s w θ) := by
    filter_upwards [hall] with t ht
    apply Finset.sum_congr rfl
    intro η hη
    simp only [ht η hη]
  exact continuousWithinAt_const.congr_of_eventuallyEq he rfl

/-- The left limit omits precisely the weight at the endpoint. -/
theorem density_tendsto_left (s : Finset ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    Filter.Tendsto (density s w) (nhdsWithin θ (Iio θ))
      (nhds (density s w θ - if θ ∈ s then w θ else 0)) := by
  classical
  let L : ℝ := ∑ η ∈ s, if η < θ then w η else 0
  have hL : L = density s w θ - if θ ∈ s then w θ else 0 := by
    have he : ∀ η : ℝ, (if η < θ then w η else 0) =
        (if η ≤ θ then w η else 0) - (if η = θ then w η else 0) := by
      intro η
      rcases lt_trichotomy η θ with hlt | heq | hgt
      · simp [hlt, hlt.le, ne_of_lt hlt]
      · simp [heq]
      · simp [not_lt_of_ge hgt.le, not_le_of_gt hgt, ne_of_gt hgt]
    dsimp [L, density]
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp
  have hall : ∀ᶠ t in nhdsWithin θ (Iio θ), ∀ η ∈ s, (η ≤ t ↔ η < θ) := by
    rw [Filter.eventually_all_finset]
    intro η hη
    by_cases hlt : η < θ
    · have hm : Ioi η ∈ nhds θ := isOpen_Ioi.mem_nhds hlt
      filter_upwards [nhdsWithin_le_nhds hm] with t ht
      exact ⟨fun _ => hlt, fun _ => ht.le⟩
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hn : ¬ η ≤ t := not_le_of_gt (lt_of_lt_of_le ht (not_lt.mp hlt))
      exact iff_of_false hn hlt
  have he : (fun _ : ℝ => L) =ᶠ[nhdsWithin θ (Iio θ)] density s w := by
    filter_upwards [hall] with t ht
    dsimp [L]
    symm
    apply Finset.sum_congr rfl
    intro η hη
    simp only [ht η hη]
  rw [← hL]
  exact Filter.Tendsto.congr' he tendsto_const_nhds

/-- The actual nonzero jump positions are exactly the discontinuities. -/
theorem density_continuousAt_iff (s : Finset ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    ContinuousAt (density s w) θ ↔ θ ∉ activeJumps s w := by
  classical
  constructor
  · intro hc
    have he := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (density_tendsto_left s w θ)
    by_cases hs : θ ∈ s
    · have hz : w θ = 0 := by
        simp only [if_pos hs] at he
        linarith
      simp [mem_activeJumps, hz]
    · simp [mem_activeJumps, hs]
  · intro hn
    have hc := density_continuousAt (activeJumps s w) w hn
    have he : density (activeJumps s w) w = density s w :=
      funext (density_activeJumps s w)
    rw [he] at hc
    exact hc

/-- A nonempty positive finite jump family has a positive increment between
continuity points strictly inside its ambient interval. -/
theorem exists_positive_interval (s : Finset ℝ) (w : ℝ → ℝ) {l u : ℝ}
    (hne : s.Nonempty) (hin : ∀ η ∈ s, η ∈ Ioo l u)
    (hw : ∀ η ∈ s, 0 < w η) :
    ∃ α₁ α₂ : ℝ, l < α₁ ∧ α₁ < α₂ ∧ α₂ < u ∧
      ContinuousAt (density s w) α₁ ∧ ContinuousAt (density s w) α₂ ∧
      0 < density s w α₂ - density s w α₁ := by
  classical
  obtain ⟨η, hη⟩ := hne
  have hlu : l < u := (hin η hη).1.trans (hin η hη).2
  have hl : ∀ ξ ∈ s, ξ ∉ Icc l l := by
    intro ξ hξ hh
    exact (not_le_of_gt (hin ξ hξ).1) hh.2
  have hu : ∀ ξ ∈ s, ξ ∉ Icc u u := by
    intro ξ hξ hh
    exact (not_le_of_gt (hin ξ hξ).2) hh.1
  obtain ⟨δl, hδl, hbl⟩ := finite_buffer s le_rfl hl
  obtain ⟨δu, hδu, hbu⟩ := finite_buffer s le_rfl hu
  let δ := min δl (min δu ((u-l)/4))
  have hδ : 0 < δ := lt_min hδl (lt_min hδu (by linarith))
  have hδl' : δ ≤ δl := min_le_left _ _
  have hδu' : δ ≤ δu := (min_le_right _ _).trans (min_le_left _ _)
  have hδq : δ ≤ (u-l)/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hlow : ∀ ξ ∈ s, l+δ < ξ := by
    intro ξ hξ
    have hh := hbl ξ hξ
    have hξl := (hin ξ hξ).1
    by_contra hn
    apply hh
    exact ⟨by linarith, by linarith [le_of_not_gt hn]⟩
  have hhigh : ∀ ξ ∈ s, ξ < u-δ := by
    intro ξ hξ
    have hh := hbu ξ hξ
    have hξu := (hin ξ hξ).2
    by_contra hn
    apply hh
    exact ⟨by linarith [le_of_not_gt hn], by linarith⟩
  have hc₁ : ContinuousAt (density s w) (l+δ) := by
    apply density_continuousAt
    intro hm
    exact (lt_irrefl _) (hlow _ hm)
  have hc₂ : ContinuousAt (density s w) (u-δ) := by
    apply density_continuousAt
    intro hm
    exact (lt_irrefl _) (hhigh _ hm)
  refine ⟨l+δ, u-δ, by linarith, by linarith, by linarith, hc₁, hc₂, ?_⟩
  have he₁ : density s w (l+δ) = 0 := by
    unfold density
    apply Finset.sum_eq_zero
    intro ξ hξ
    simp [not_le_of_gt (hlow ξ hξ)]
  have he₂ : density s w (u-δ) = ∑ ξ ∈ s, w ξ := by
    unfold density
    apply Finset.sum_congr rfl
    intro ξ hξ
    simp [(hhigh ξ hξ).le]
  rw [he₁, he₂, sub_zero]
  exact Finset.sum_pos hw ⟨η, hη⟩

#print axioms exists_positive_interval
#print axioms density_tendsto_left
#print axioms density_continuousAt_iff
#print axioms density_monotone
#print axioms density_eq_of_no_jumps
#print axioms finite_buffer
#print axioms density_constant_on_Icc
#print axioms buffered_density
#print axioms density_locally_constant
#print axioms density_continuousAt
#print axioms mem_activeJumps
#print axioms density_activeJumps
#print axioms buffered_density_activeJumps
#print axioms density_continuousWithinAt_right

end ZeroDensity.FiniteJumps
