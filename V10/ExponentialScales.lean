import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Exponential scale comparisons for v10

These are unconditional real-analysis lemmas used in Theorem 1.3,
Corollary 7.2, and in comparing the active and inactive frequencies in
Theorem 1.4. They do not assert any zero-count estimate from an ODE.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace V10.ExponentialScales

def scale (a β r : ℝ) : ℝ := r ^ β * Real.exp (a * r)

lemma scale_pos (a β : ℝ) {r : ℝ} (hr : 0 < r) : 0 < scale a β r :=
  mul_pos (Real.rpow_pos_of_pos hr β) (Real.exp_pos _)

lemma ratio_eq {r : ℝ} (hr : 0 < r) (a b N η : ℝ) :
    scale b N r / scale a η r =
      r ^ (N - η) * Real.exp (-(a - b) * r) := by
  unfold scale
  calc
    r ^ N * Real.exp (b * r) / (r ^ η * Real.exp (a * r)) =
        (r ^ N / r ^ η) * (Real.exp (b * r) / Real.exp (a * r)) := by ring
    _ = r ^ (N - η) * Real.exp (b * r - a * r) := by
      rw [Real.rpow_sub hr, Real.exp_sub]
    _ = _ := by congr 2; ring

/-- Any strict exponential gap defeats any fixed real polynomial powers. -/
theorem ratio_tendsto_zero {a b : ℝ} (hba : b < a) (N η : ℝ) :
    Tendsto (fun r => scale b N r / scale a η r) atTop (𝓝 0) := by
  apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (N - η) (a - b) (sub_pos.mpr hba)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (ratio_eq hr a b N η).symm

theorem scale_isLittleO {a b : ℝ} (hba : b < a) (N η : ℝ) :
    scale b N =o[atTop] scale a η := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact fun h => ((scale_pos a η hr).ne' h).elim
  · exact ratio_tendsto_zero hba N η

/-- A signed error bounded by the discarded count is negligible on every
    leading scale with a strictly larger exponential rate. -/
theorem negligible_of_exp_bound {f : ℝ → ℝ} {a b C N η : ℝ}
    (hba : b < a)
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * scale b N r) :
    f =o[atTop] scale a η := by
  have hO : f =O[atTop] scale b N := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hf, eventually_gt_atTop (0 : ℝ)] with r h hr
    simpa only [Real.norm_eq_abs, abs_of_pos (scale_pos b N hr)] using h
  exact hO.trans_isLittleO (scale_isLittleO hba N η)

/-- Lower polynomial order at the same exponential rate is negligible. -/
theorem lower_power_ratio_tendsto_zero (a : ℝ) {β γ : ℝ} (hβγ : β < γ) :
    Tendsto (fun r => scale a β r / scale a γ r) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r ^ (β - γ)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hβγ)
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [ratio_eq hr]
  simp

/-- The global scale printed in v10, with its actual `a` normalization. -/
def globalScale (a β r : ℝ) : ℝ :=
  (a * r) ^ (β + 1 / 2) * Real.exp (a * r)

theorem globalScale_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (β : ℝ) :
    globalScale a β r = a ^ (β + 1 / 2) * scale a (β + 1 / 2) r := by
  rw [globalScale, Real.mul_rpow ha.le hr.le]
  unfold scale
  ring

end V10.ExponentialScales
