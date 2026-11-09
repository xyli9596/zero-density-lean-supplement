import V10.ScalarCompactnessJensen
import V10.ScalarAnalytic
import V10.ScalarLogSubmean

/-!
# Quantitative L¹ bounds for analytic logarithms

A genuine analytic norm upper bound and one nonzero center lower bound give
an L¹ bound by the disk submean inequality. All local integrability and
zero-set-nullity inputs are derived from analyticity and the center value.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace V10.ScalarCompactnessL1Bounds

theorem log_inputs_on_disk_of_point {f : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hw : w ∈ closedBall c r) (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfw : f w ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall c r) ∧
      (∀ᵐ z ∂volume.restrict (closedBall c r), f z ≠ 0) := by
  have hg : ∀ z ∈ closedBall c r, ¬f =ᶠ[𝓝 z] 0 := by
    intro z hz he
    exact hfw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c r).isPreconnected hz he hw)
  exact ⟨(ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm hf hg).integrableOn_isCompact
    (isCompact_closedBall c r),
    ScalarAnalytic.ae_ne_zero_of_germs measurableSet_closedBall hf hg⟩

theorem log_inputs_on_disk {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfc : f c ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall c r) ∧
      (∀ᵐ z ∂volume.restrict (closedBall c r), f z ≠ 0) :=
  log_inputs_on_disk_of_point (mem_closedBall_self hr) hf hfc

/-- Elementary conversion of an upper bound and an integral lower bound into
an L¹ norm bound. This is used with the actual submean inequality below. -/
theorem integral_abs_le_of_upper_and_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {B C : ℝ}
    (hi : Integrable u μ) (hB : 0 ≤ B) (hu : ∀ᵐ z ∂μ, u z ≤ B)
    (hl : -C * μ.real univ ≤ ∫ z, u z ∂μ) :
    (∫ z, |u z| ∂μ) ≤ (2 * B + C) * μ.real univ := by
  have hb : ∀ᵐ z ∂μ, |u z| ≤ 2 * B - u z := by
    filter_upwards [hu] with z hz
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := integral_mono_ae hi.abs ((integrable_const (2 * B)).sub hi) hb
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const (2 * B)) hi, integral_const] at h
  simp only [smul_eq_mul] at h
  linarith

/-- Normalized analytic logarithms have a uniform L¹ bound on a disk from
actual exponential upper bounds there and a single exponential lower bound
at its center. This applies unchanged when the center varies with a sequence. -/
theorem normalized_log_integral_abs_le {f : ℂ → ℂ} {c : ℂ} {r q B C : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hupper : ∀ z ∈ closedBall c r, ‖f z‖ ≤ Real.exp (q * B))
    (hlower : Real.exp (-q * C) ≤ ‖f c‖) :
    (∫ z in closedBall c r, |Real.log ‖f z‖ / q|) ≤
      (2 * B + C) * volume.real (closedBall c r) := by
  let : IsFiniteMeasure (volume.restrict (closedBall c r)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall c r).measure_ne_top
  have hfc : f c ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hlower)
  obtain ⟨hi, hz⟩ := log_inputs_on_disk hr.le hf hfc
  have hmean := ScalarLogSubmean.normalized_log_norm_le_disk_average hr hq hf hfc hz hi
  have hl : -C ≤ Real.log ‖f c‖ / q := by
    have h := Real.log_le_log (Real.exp_pos _) hlower
    rw [Real.log_exp] at h
    exact (le_div_iff₀ hq).mpr (by nlinarith)
  have hm : 0 < volume.real (closedBall c r) := by
    rw [Complex.volume_closedBall' hr.le]
    positivity
  have hlint : -C * (volume.restrict (closedBall c r)).real univ ≤
      ∫ z in closedBall c r, Real.log ‖f z‖ / q := by
    have h := hl.trans hmean
    rw [setAverage_eq, smul_eq_mul] at h
    rw [measureReal_restrict_apply_univ]
    apply (le_div_iff₀ hm).mp
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hu : ∀ᵐ z ∂volume.restrict (closedBall c r), Real.log ‖f z‖ / q ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall, hz] with z hzD hzn
    apply (div_le_iff₀ hq).mpr
    have h := Real.log_le_log (norm_pos_iff.mpr hzn) (hupper z hzD)
    simpa only [Real.log_exp, mul_comm] using h
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    integral_abs_le_of_upper_and_lower (hi.div_const q) hB hu hlint

end V10.ScalarCompactnessL1Bounds
