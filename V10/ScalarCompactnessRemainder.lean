import V10.ScalarCompactnessDivisor
import V10.ScalarCompactnessL1Bounds
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The harmonic remainder of actual analytic logarithms

The finite divisor is extracted from the analytic function itself. We identify
its logarithmic part with the actual L¹ potential and bound the L¹ norm of
the resulting harmonic remainder; no Riesz decomposition is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology

namespace V10.ScalarCompactnessRemainder
open ScalarCompactnessLogPotential ScalarCompactnessJensen ScalarCompactnessDivisor
open ScalarCompactnessL1Bounds

theorem norm_divisorPotential_le {f : ℂ → ℂ} {c : ℂ} {r q cutoff : ℝ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    ‖divisorPotential f c r q cutoff‖ ≤
      (∑ u ∈ divisorSupport f c r,
        (MeromorphicOn.divisor f (closedBall c r) u : ℝ) / q) * ‖cutoffLogL1 cutoff‖ := by
  apply norm_sum_logKernel_le
  intro u _
  apply div_nonneg _ hq.le
  exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u

theorem divisorPotential_ae_eq_on_disk {f : ℂ → ℂ} {c : ℂ} {r q : ℝ} (hr : 0 < r) :
    (divisorPotential f c r q (3 * r) : ℂ → ℝ) =ᵐ[volume.restrict (closedBall c r)]
      fun z => ∑ u ∈ divisorSupport f c r,
        ((MeromorphicOn.divisor f (closedBall c r) u : ℝ) / q) * Real.log ‖z - u‖ := by
  apply sum_logKernel_ae_eq_on _ _ _ measurableSet_closedBall
  intro u hu z hz
  have hu' := divisorSupport_subset f c r hu
  have hdist : dist z u ≤ 2 * r := by
    calc
      dist z u ≤ dist z c + dist c u := dist_triangle z c u
      _ ≤ r + r := add_le_add (mem_closedBall.mp hz)
        (by simpa only [dist_comm] using mem_closedBall.mp hu')
      _ = 2 * r := by ring
  rw [← dist_eq_norm]
  exact lt_of_le_of_lt hdist (by linarith)

/-- The decomposition and the harmonic remainder are derived from the
actual analytic function, allowing the nonzero point to move in the disk. -/
theorem exists_harmonic_remainder {f : ℂ → ℂ} {c w : ℂ} {r q : ℝ}
    (hr : 0 < r) (_hq : 0 < q) (hw : w ∈ closedBall c r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfw : f w ≠ 0) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h (closedBall c r) ∧
      (fun z => Real.log ‖f z‖ / q) =ᵐ[volume.restrict (closedBall c r)]
        (fun z => divisorPotential f c r q (3 * r) z + h z) ∧
      (∫ z in closedBall c r, ‖h z‖) ≤
        (∫ z in closedBall c r, |Real.log ‖f z‖ / q|) +
          ‖divisorPotential f c r q (3 * r)‖ := by
  classical
  obtain ⟨g, hg, hgn, he⟩ := analytic_log_divisor_decomposition_of_point hw hf hfw
  let h : ℂ → ℝ := fun z => Real.log ‖g z‖ / q
  have hh : HarmonicOnNhd h (closedBall c r) := by
    have hhg : HarmonicOnNhd (fun z => Real.log ‖g z‖) (closedBall c r) :=
      fun z hz => (hg z hz).harmonicAt_log_norm (hgn z hz)
    convert hhg.const_smul (c := q⁻¹) using 1
    ext z
    simp only [h, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hs : Function.support (fun u => (fun z =>
      (MeromorphicOn.divisor f (closedBall c r) u : ℝ) * Real.log ‖z - u‖)) ⊆
      (divisorSupport f c r : Set ℂ) := by
    intro u hu
    apply mem_divisorSupport.mpr
    intro hzero
    apply hu
    ext z
    simp [hzero]
  rw [finsum_eq_sum_of_support_subset _ hs] at he
  have hrep : (fun z => Real.log ‖f z‖ / q) =ᵐ[volume.restrict (closedBall c r)]
      (fun z => divisorPotential f c r q (3 * r) z + h z) := by
    filter_upwards [he, divisorPotential_ae_eq_on_disk (f := f) (q := q) hr] with z hz hp
    rw [hz]
    simp only [Pi.add_apply, Finset.sum_apply, add_div, h]
    rw [hp, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    ring
  refine ⟨h, hh, hrep, ?_⟩
  have hi := (log_inputs_on_disk_of_point hw hf hfw).1.div_const q
  have hip : Integrable (divisorPotential f c r q (3 * r) : ℂ → ℝ) :=
    MeasureTheory.L1.integrable_coeFn _
  have hipD : IntegrableOn (divisorPotential f c r q (3 * r) : ℂ → ℝ)
      (closedBall c r) := hip.mono_measure Measure.restrict_le_self
  have hih : IntegrableOn h (closedBall c r) :=
    hh.continuousOn.integrableOn_compact (isCompact_closedBall c r)
  have htri : ∀ᵐ z ∂volume.restrict (closedBall c r), ‖h z‖ ≤
      |Real.log ‖f z‖ / q| + ‖divisorPotential f c r q (3 * r) z‖ := by
    filter_upwards [hrep] with z hz
    have heq : h z = Real.log ‖f z‖ / q - divisorPotential f c r q (3 * r) z := by
      linarith
    rw [heq]
    exact (norm_sub_le _ _).trans_eq (by rw [Real.norm_eq_abs])
  have hI := integral_mono_ae hih.norm (hi.abs.add hipD.norm) htri
  simp only [Pi.add_apply] at hI
  rw [integral_add hi.abs hipD.norm] at hI
  have hP : (∫ z in closedBall c r, ‖divisorPotential f c r q (3 * r) z‖) ≤
      ‖divisorPotential f c r q (3 * r)‖ := by
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun z => norm_nonneg _) hip.norm
  exact hI.trans (add_le_add le_rfl hP)

end V10.ScalarCompactnessRemainder
