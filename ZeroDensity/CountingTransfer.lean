import ZeroDensity.RadiusComparison

namespace ZeroDensity.CountingTransfer
open Filter
open scoped Topology
noncomputable section

lemma small_multiplier (c : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε * |c| < d := by
  have hm : 0 < min 1 (d / (|c| + 1)) := lt_min (by norm_num)
    (div_pos hd (by positivity))
  obtain ⟨ε, hε0, hε⟩ := exists_between hm
  refine ⟨ε, hε0, hε.trans_le (min_le_left _ _), ?_⟩
  have he : ε < d / (|c| + 1) := hε.trans_le (min_le_right _ _)
  have hem : ε * (|c| + 1) < d := (lt_div_iff₀ (by positivity)).mp he
  nlinarith [abs_nonneg c]

/-- A fixed multiplicative rescaling of the cutoff rescales the phase count law. -/
lemma scaled_phase_law {nPhase q : ℝ → ℝ} {c k : ℝ} (hk : 0 < k)
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun s => nPhase s / s) atTop (𝓝 c)) :
    Tendsto (fun r => nPhase (k * q r) / q r) atTop (𝓝 (k * c)) := by
  have ht := (hn.comp (hq.const_mul_atTop hk)).const_mul k
  refine ht.congr' ?_
  filter_upwards [hq.eventually_gt_atTop 0] with r hr
  dsimp
  field_simp

/-- Transfer a phase counting law through two multiplicative cutoffs and a fixed
finite error. No strict positivity of the limiting density is required. -/
theorem count_law_transfer {nPhase N q : ℝ → ℝ} {c C : ℝ}
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun s => nPhase s / s) atTop (𝓝 c))
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ r in atTop,
      nPhase ((1 - ε) * q r) - C ≤ N r ∧
      N r ≤ nPhase ((1 + ε) * q r) + C) :
    Tendsto (fun r => N r / q r) atTop (𝓝 c) := by
  have hC : Tendsto (fun r => C / q r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hq
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨ε, hε0, hε1, he⟩ := small_multiplier c (sub_pos.mpr hl)
    have hc : l < (1 - ε) * c := by
      have hca := le_abs_self c
      nlinarith
    have ht : Tendsto (fun r => (nPhase ((1 - ε) * q r) - C) / q r)
        atTop (𝓝 ((1 - ε) * c)) := by
      simpa only [sub_div, sub_zero] using
        (scaled_phase_law (by linarith : 0 < 1 - ε) hq hn).sub hC
    filter_upwards [hsand ε hε0 hε1, hq.eventually_gt_atTop 0,
      ht.eventually (eventually_gt_nhds hc)] with r hs hr ht
    exact ht.trans_le ((div_le_div_iff_of_pos_right hr).mpr hs.1)
  · intro u hu
    obtain ⟨ε, hε0, hε1, he⟩ := small_multiplier c (sub_pos.mpr hu)
    have hc : (1 + ε) * c < u := by
      have hca := le_abs_self c
      nlinarith
    have ht : Tendsto (fun r => (nPhase ((1 + ε) * q r) + C) / q r)
        atTop (𝓝 ((1 + ε) * c)) := by
      simpa only [add_div, add_zero] using
        (scaled_phase_law (by linarith : 0 < 1 + ε) hq hn).add hC
    filter_upwards [hsand ε hε0 hε1, hq.eventually_gt_atTop 0,
      ht.eventually (eventually_lt_nhds hc)] with r hs hr ht
    exact ((div_le_div_iff_of_pos_right hr).mpr hs.2).trans_lt ht

/-- The count scale as printed in the main zero-count asymptotic. -/
def mainScale (a β r : ℝ) : ℝ := r ^ β * Real.exp (a * r)

lemma mainScale_pos {a r : ℝ} (hr : 0 < r) (β : ℝ) : 0 < mainScale a β r :=
  mul_pos (Real.rpow_pos_of_pos hr β) (Real.exp_pos _)

lemma Q_eq_mainScale {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (β : ℝ) :
    RadiusComparison.Q a β r = a ^ β * mainScale a β r := by
  unfold RadiusComparison.Q mainScale
  rw [Real.mul_rpow ha.le hr.le]
  ring

/-- Conversion from the phase normalization to the theorem's radius normalization. -/
theorem main_scale_law {a β c : ℝ} (ha : 0 < a) {N : ℝ → ℝ}
    (hN : Tendsto (fun r => N r / RadiusComparison.Q a β r) atTop (𝓝 c)) :
    Tendsto (fun r => N r / mainScale a β r) atTop (𝓝 (a ^ β * c)) := by
  refine (hN.const_mul (a ^ β)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Q_eq_mainScale ha hr]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos ha β)]

/-- Normalized count convergence and a little-o error are equivalent. -/
theorem main_scale_law_iff_littleO {a β d : ℝ} {N : ℝ → ℝ} :
    Tendsto (fun r => N r / mainScale a β r) atTop (𝓝 d) ↔
    (fun r => N r - d * mainScale a β r) =o[atTop] (mainScale a β) := by
  have hnz : ∀ᶠ r in atTop, mainScale a β r ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact ne_of_gt (mainScale_pos hr β)
  have heq : ∀ᶠ r in atTop,
      (N r - d * mainScale a β r) / mainScale a β r = N r / mainScale a β r - d := by
    filter_upwards [hnz] with r hr
    field_simp
  rw [Asymptotics.isLittleO_iff_tendsto' (hnz.mono fun r hr hz => (hr hz).elim)]
  constructor
  · intro ht
    have ht' : Tendsto (fun r => N r / mainScale a β r - d) atTop (𝓝 0) := by
      simpa using ht.sub_const d
    exact ht'.congr' (heq.mono fun r h => h.symm)
  · intro ht
    have ht' : Tendsto (fun r => N r / mainScale a β r - d) atTop (𝓝 0) :=
      ht.congr' heq
    simpa using ht'.add_const d

/-- Explicit conditional assembly: a phase law and actual counting cutoffs imply
both the main normalized law and its equivalent little-o formulation. -/
theorem transferred_main_law {a β c C : ℝ} (ha : 0 < a) {nPhase N : ℝ → ℝ}
    (hn : Tendsto (fun s => nPhase s / s) atTop (𝓝 c))
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ r in atTop,
      nPhase ((1 - ε) * RadiusComparison.Q a β r) - C ≤ N r ∧
      N r ≤ nPhase ((1 + ε) * RadiusComparison.Q a β r) + C) :
    Tendsto (fun r => N r / mainScale a β r) atTop (𝓝 (a ^ β * c)) ∧
    (fun r => N r - (a ^ β * c) * mainScale a β r) =o[atTop] (mainScale a β) := by
  have ht := main_scale_law ha
    (count_law_transfer (RadiusComparison.Q_tendsto ha β) hn hsand)
  exact ⟨ht, main_scale_law_iff_littleO.mp ht⟩

end
end ZeroDensity.CountingTransfer
