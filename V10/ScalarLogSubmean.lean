module
public import Ray.Hartogs.Subharmonic
public import Ray.Hartogs.MaxLog
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-!+# Disk submean inequalities for scalar analytic logarithms

The integral uses the real-valued representative `Real.log ‖f z‖`. At zeros,
this representative is not the subharmonic point value. All center estimates
therefore explicitly require a nonzero center; the integral is unchanged by
altering values on the null zero set. Continuous Ray truncations are used to
prove the inequalities, rather than assuming subharmonicity of `Real.log 0`.
-/

public section
noncomputable section
open Filter MeasureTheory Metric Set
open scoped Topology
namespace V10.ScalarLogSubmean

lemma maxLog_eq_max_log {b x : ℝ} (hx : 0 < x) :
    maxLog b x = max b (Real.log x) := by
  by_cases h : Real.exp b ≤ x
  · rw [maxLog_eq_log h, max_eq_right ((Real.le_log_iff_exp_le hx).2 h)]
  · have h' : x ≤ Real.exp b := le_of_lt (lt_of_not_ge h)
    rw [maxLog_eq_b h', max_eq_left ((Real.log_le_iff_le_exp hx).2 h')]

lemma abs_max_neg_nat_le (n : ℕ) (x : ℝ) :
    |max (-(n : ℝ)) x| ≤ |x| := by
  rcases le_total (-(n : ℝ)) x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, abs_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg n)), abs_of_nonpos]
    · linarith
    · exact h.trans (neg_nonpos.mpr (Nat.cast_nonneg n))

/-- Lower truncations converge in integral to any integrable real function.
This is a dominated-convergence result, not a compactness assumption. -/
theorem integral_lower_truncation_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : α → ℝ} (hu : Integrable u μ) :
    Tendsto (fun n : ℕ => ∫ x, max (-(n : ℝ)) (u x) ∂μ) atTop
      (𝓝 (∫ x, u x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |u x|)
  · intro n
    exact (continuous_const.max continuous_id).comp_aestronglyMeasurable hu.aestronglyMeasurable
  · exact hu.abs
  · intro n
    exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using abs_max_neg_nat_le n (u x)
  · exact ae_of_all _ fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈-u x⌉₊)] with n hn
      have hb : -u x ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      exact (max_eq_right (by linarith : -(n : ℝ) ≤ u x)).symm

/-- Actual analytic log modulus lies below its disk average at nonzero centers.
Nullity of the zero set and log integrability are the precise measure-theoretic
inputs; the submean inequality itself is proved from analytic truncations. -/
theorem log_norm_le_disk_average {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hc : f c ≠ 0)
    (hz : ∀ᵐ z ∂volume.restrict (closedBall c r), f z ≠ 0)
    (hi : IntegrableOn (fun z => Real.log ‖f z‖) (closedBall c r)) :
    Real.log ‖f c‖ ≤ ⨍ z in closedBall c r, Real.log ‖f z‖ := by
  have hlim := integral_lower_truncation_tendsto hi
  have hlim' : Tendsto (fun n : ℕ => ⨍ z in closedBall c r,
      max (-(n : ℝ)) (Real.log ‖f z‖)) atTop
      (𝓝 (⨍ z in closedBall c r, Real.log ‖f z‖)) := by
    simp only [setAverage_eq, smul_eq_mul]
    exact hlim.const_mul _
  apply ge_of_tendsto hlim'
  filter_upwards [eventually_ge_atTop (⌈-Real.log ‖f c‖⌉₊)] with n hn
  have hb : -(n : ℝ) ≤ Real.log ‖f c‖ := by
    have := (Nat.le_ceil (-Real.log ‖f c‖)).trans (show (⌈-Real.log ‖f c‖⌉₊ : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  have hs := (hf.maxLog_norm_subharmonicOn (-(n : ℝ))).submean_disk hr
  rw [maxLog_eq_max_log (norm_pos_iff.mpr hc), max_eq_right hb] at hs
  have heq : (⨍ z in closedBall c r, maxLog (-(n : ℝ)) ‖f z‖) =
      ⨍ z in closedBall c r, max (-(n : ℝ)) (Real.log ‖f z‖) := by
    apply average_congr
    filter_upwards [hz] with z hzn
    exact maxLog_eq_max_log (norm_pos_iff.mpr hzn)
  rw [heq] at hs
  exact hs

theorem normalized_log_norm_le_disk_average {f : ℂ → ℂ} {c : ℂ} {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hc : f c ≠ 0)
    (hz : ∀ᵐ z ∂volume.restrict (closedBall c r), f z ≠ 0)
    (hi : IntegrableOn (fun z => Real.log ‖f z‖) (closedBall c r)) :
    Real.log ‖f c‖ / q ≤ ⨍ z in closedBall c r, Real.log ‖f z‖ / q := by
  have h := div_le_div_of_nonneg_right (log_norm_le_disk_average hr hf hc hz hi) hq.le
  simpa only [setAverage_eq, smul_eq_mul, integral_div, mul_div_assoc] using h

#print axioms integral_lower_truncation_tendsto
#print axioms log_norm_le_disk_average
#print axioms normalized_log_norm_le_disk_average
end V10.ScalarLogSubmean
