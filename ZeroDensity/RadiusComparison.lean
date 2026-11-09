import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ZeroDensity.RadiusComparison
open Filter
open scoped Topology
noncomputable section

def Q (a β r : ℝ) : ℝ := (a * r) ^ β * Real.exp (a * r)
def L (a β R : ℝ) : ℝ := (Real.log R - β * Real.log (Real.log R)) / a

lemma Q_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (β : ℝ) : 0 < Q a β r := by
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos ha hr) β) (Real.exp_pos _)

lemma log_Q {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (β : ℝ) :
    Real.log (Q a β r) = a * r + β * Real.log (a * r) := by
  rw [Q, Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (mul_pos ha hr) β))
    (Real.exp_ne_zero _), Real.log_rpow (mul_pos ha hr), Real.log_exp]
  ring

lemma Q_tendsto {a : ℝ} (ha : 0 < a) (β : ℝ) :
    Tendsto (Q a β) atTop atTop := by
  have ht : Tendsto (fun r : ℝ => a * r) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  refine ((tendsto_exp_div_rpow_atTop (-β)).comp ht).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [Function.comp_apply, Q, Real.rpow_neg (mul_pos ha hr).le, div_inv_eq_mul, mul_comm]

lemma log_Q_ratio_tendsto {a : ℝ} (ha : 0 < a) (β : ℝ) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r => Real.log (k * Q a β r) / (a * r)) atTop (𝓝 1) := by
  have ht : Tendsto (fun r : ℝ => a * r) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hlog : Tendsto (fun r => Real.log (a * r) / (a * r)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht
  have hc : Tendsto (fun r => Real.log k / (a * r)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hs' : Tendsto (fun r => Real.log k / (a * r) +
      (1 + β * (Real.log (a * r) / (a * r)))) atTop (𝓝 1) := by
    simpa using (hc.add ((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := β)).mul hlog)))
  refine hs'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.log_mul (ne_of_gt hk) (ne_of_gt (Q_pos ha hr β)), log_Q ha hr]
  field_simp

/-- Multiplying the phase radius by a fixed positive factor translates the inverse
radius by `log k / a`, including the logarithmic correction. -/
theorem inverse_radius_shift {a : ℝ} (ha : 0 < a) (β : ℝ) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r => L a β (k * Q a β r) - r) atTop (𝓝 (Real.log k / a)) := by
  have hratio := log_Q_ratio_tendsto ha β hk
  have hlogratio : Tendsto (fun r => Real.log
      (Real.log (k * Q a β r) / (a * r))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlim : Tendsto (fun r =>
      (Real.log k - β * Real.log (Real.log (k * Q a β r) / (a * r))) / a)
      atTop (𝓝 (Real.log k / a)) := by
    simpa using ((tendsto_const_nhds (x := Real.log k)).sub
      ((tendsto_const_nhds (x := β)).mul hlogratio)).div_const a
  have hlarge : Tendsto (fun r => Real.log (k * Q a β r)) atTop atTop :=
    Real.tendsto_log_atTop.comp ((Q_tendsto ha β).const_mul_atTop hk)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlarge.eventually_gt_atTop 0] with r hr hl
  rw [Real.log_div (ne_of_gt hl) (ne_of_gt (mul_pos ha hr))]
  unfold L
  rw [Real.log_mul (ne_of_gt hk) (ne_of_gt (Q_pos ha hr β)), log_Q ha hr]
  field_simp
  ring

/-- The upper cutoff displacement is positive. -/
lemma upper_shift_pos {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    0 < Real.log (1 + ε) / a := by
  exact div_pos (Real.log_pos (by linarith)) ha

/-- The lower cutoff displacement is negative. -/
lemma lower_shift_neg {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log (1 - ε) / a < 0 := by
  exact div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) ha

/-- A uniform vanishing inverse-radius error preserves a strictly positive cutoff
shift. The index type can represent the entire closed angular interval. -/
theorem eventually_upper_cutoff {ι : Type*} {a β k : ℝ} (ha : 0 < a) (hk : 1 < k)
    {F : ℝ → ι → ℝ} {E : ℝ → ℝ} (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ r in atTop, ∀ i, |F r i - L a β (k * Q a β r)| ≤ E r) :
    ∀ᶠ r in atTop, ∀ i, r < F r i := by
  have hk0 : 0 < k := by linarith
  have hshift := inverse_radius_shift ha β hk0
  have hc : 0 < Real.log k / a := div_pos (Real.log_pos hk) ha
  have ht : Tendsto (fun r => (L a β (k * Q a β r) - r) - E r)
      atTop (𝓝 (Real.log k / a)) := by simpa using hshift.sub hE
  filter_upwards [herr, ht.eventually (eventually_gt_nhds hc)] with r he ht i
  have hi := (abs_le.mp (he i)).1
  linarith

/-- A uniform vanishing inverse-radius error preserves a strictly negative cutoff
shift. This is the lower containment in the zero-count sandwich. -/
theorem eventually_lower_cutoff {ι : Type*} {a β k : ℝ} (ha : 0 < a)
    (hk0 : 0 < k) (hk1 : k < 1) {F : ℝ → ι → ℝ} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ r in atTop, ∀ i, |F r i - L a β (k * Q a β r)| ≤ E r) :
    ∀ᶠ r in atTop, ∀ i, F r i < r := by
  have hshift := inverse_radius_shift ha β hk0
  have hc : Real.log k / a < 0 := div_neg_of_neg_of_pos (Real.log_neg hk0 hk1) ha
  have ht : Tendsto (fun r => (L a β (k * Q a β r) - r) + E r)
      atTop (𝓝 (Real.log k / a)) := by simpa using hshift.add hE
  filter_upwards [herr, ht.eventually (eventually_lt_nhds hc)] with r he ht i
  have hi := (abs_le.mp (he i)).2
  linarith

/-- The radius asymptotic is applied at the actual scaled phase cutoff. -/
theorem upper_cutoff_of_inverse_asymptotic {ι : Type*} {a β k : ℝ}
    (ha : 0 < a) (hk : 1 < k) {ρ : ℝ → ι → ℝ} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ s in atTop, ∀ i, |ρ s i - L a β s| ≤ E s) :
    ∀ᶠ r in atTop, ∀ i, r < ρ (k * Q a β r) i := by
  have hk0 : 0 < k := by linarith
  have ht := (Q_tendsto ha β).const_mul_atTop hk0
  apply eventually_upper_cutoff ha hk (hE.comp ht)
  exact ht.eventually herr

theorem lower_cutoff_of_inverse_asymptotic {ι : Type*} {a β k : ℝ}
    (ha : 0 < a) (hk0 : 0 < k) (hk1 : k < 1) {ρ : ℝ → ι → ℝ} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ s in atTop, ∀ i, |ρ s i - L a β s| ≤ E s) :
    ∀ᶠ r in atTop, ∀ i, ρ (k * Q a β r) i < r := by
  have ht := (Q_tendsto ha β).const_mul_atTop hk0
  apply eventually_lower_cutoff ha hk0 hk1 (hE.comp ht)
  exact ht.eventually herr

/-- Both angularly uniform cutoff inequalities from a single inverse-radius asymptotic. -/
theorem cutoff_sandwich {ι : Type*} {a β ε : ℝ} (ha : 0 < a)
    (hε : 0 < ε) (hε1 : ε < 1) {ρ : ℝ → ι → ℝ} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (herr : ∀ᶠ s in atTop, ∀ i, |ρ s i - L a β s| ≤ E s) :
    ∀ᶠ r in atTop, ∀ i,
      ρ ((1 - ε) * Q a β r) i < r ∧ r < ρ ((1 + ε) * Q a β r) i := by
  have hlo := lower_cutoff_of_inverse_asymptotic ha
    (by linarith : 0 < 1 - ε) (by linarith : 1 - ε < 1) hE herr
  have hhi := upper_cutoff_of_inverse_asymptotic ha (by linarith : 1 < 1 + ε) hE herr
  filter_upwards [hlo, hhi] with r hl hh i
  exact ⟨hl i, hh i⟩

end
end ZeroDensity.RadiusComparison
