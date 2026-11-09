import V10.ScalarCompactnessLogPotential
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Topology

/-!
# Analytic inputs for scalar logarithmic compactness

These results obtain a uniform normalized divisor mass bound from actual
analytic norm bounds via Jensen's inequality, and decompose the actual scalar
logarithm into a finite logarithmic potential and a nonvanishing analytic
remainder. They do not assume a divisor representation or a zero-count bound.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace V10.ScalarCompactnessJensen

/-- Jensen's inequality supplies the normalized mass bound needed by the
log-potential compactness theorem. The upper and lower bounds are on the
actual analytic function. -/
theorem normalized_divisor_mass_le {f : ℂ → ℂ} {c : ℂ} {r R q B C : ℝ}
    (hr : 0 < r) (hrR : r < R) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hupper : ∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp (q * B))
    (hlower : Real.exp (-q * C) ≤ ‖f c‖) :
    ((∑ᶠ u, MeromorphicOn.divisor f (closedBall c r) u : ℤ) : ℝ) / q ≤
      (B + C) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hfc : f c ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hlower)
  have hnorm : ‖f c‖ ≠ 0 := norm_ne_zero_iff.mpr hfc
  have hM : 1 ≤ Real.exp (q * B) := Real.one_le_exp (mul_nonneg hq.le hB)
  have hJ := AnalyticOnNhd.sum_divisor_le
    (c := c) (r := r) (R := R) (M := Real.exp (q * B))
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos hR] using hrR) hM
    (by simpa [abs_of_pos hR] using hf) hfc
    (by simpa [abs_of_pos hR] using hupper)
  rw [abs_of_pos hr, Real.log_div (Real.exp_ne_zero _) hnorm, Real.log_exp] at hJ
  have hl : -q * C ≤ Real.log ‖f c‖ := by
    simpa using Real.log_le_log (Real.exp_pos _) hlower
  have hd : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  calc
    _ ≤ ((q * B - Real.log ‖f c‖) / Real.log (R / r)) / q :=
      div_le_div_of_nonneg_right hJ hq.le
    _ ≤ (q * (B + C) / Real.log (R / r)) / q := by
      gcongr
      linarith
    _ = (B + C) / Real.log (R / r) := by field_simp

/-- A nonzero analytic function on a closed disk has a genuine finite
logarithmic-divisor decomposition, a.e. for planar area. The remainder is
analytic and nowhere zero on that disk. -/
theorem analytic_log_divisor_decomposition_of_point {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hw : w ∈ closedBall c R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfw : f w ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict (closedBall c R)]
        ((∑ᶠ u, (fun z => (MeromorphicOn.divisor f (closedBall c R) u : ℝ) *
          Real.log ‖z - u‖)) + fun z => Real.log ‖g z‖) := by
  have ho : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hw).meromorphicOrderAt_eq]
    simp [(hf w hw).analyticOrderAt_eq_zero.mpr hfw]
  have hall : ∀ z : closedBall c R, meromorphicOrderAt f z ≠ ⊤ := fun z =>
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hw z.property ho
  obtain ⟨g, hg, hgn, he⟩ := hf.meromorphicOn.extract_zeros_poles hall
    ((MeromorphicOn.divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R))
  refine ⟨g, hg, fun z hz => hgn ⟨z, hz⟩, ?_⟩
  exact ae_restrict_le_codiscreteWithin measurableSet_closedBall
    (MeromorphicOn.extract_zeros_poles_log hgn he)

theorem analytic_log_divisor_decomposition {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict (closedBall c R)]
        ((∑ᶠ u, (fun z => (MeromorphicOn.divisor f (closedBall c R) u : ℝ) *
          Real.log ‖z - u‖)) + fun z => Real.log ‖g z‖) :=
  analytic_log_divisor_decomposition_of_point (mem_closedBall_self hR) hf hfc

end V10.ScalarCompactnessJensen
