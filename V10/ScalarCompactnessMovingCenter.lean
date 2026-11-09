import V10.ScalarCompactnessDivisor
import V10.ScalarCompactnessL1Bounds
import V10.ScalarCauchyNoncollapse
import Mathlib.Tactic

/-!+# Uniform Jensen bounds with moving nonzero sample points

The scalar Cauchy estimate supplies a point in a small disk whose normalized
logarithm is bounded below. That point may move with the scale. Jensen's
inequality on disks centered at that point still controls the actual divisor
on a common disk, with a radius ratio independent of the point.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace V10.ScalarCompactnessMovingCenter
set_option backward.isDefEq.respectTransparency false

theorem divisor_sum_mono {f : ℂ → ℂ} {c d : ℂ} {r s : ℝ}
    (hsub : closedBall c r ⊆ closedBall d s)
    (hf : AnalyticOnNhd ℂ f (closedBall d s)) :
    (∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z) ≤
      ∑ᶠ z, MeromorphicOn.divisor f (closedBall d s) z := by
  apply finsum_le_finsum'
    ((MeromorphicOn.divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r))
    ((MeromorphicOn.divisor f (closedBall d s)).finiteSupport (isCompact_closedBall d s))
  intro z
  by_cases hz : z ∈ closedBall c r
  · rw [MeromorphicOn.divisor_apply (hf.mono hsub).meromorphicOn hz,
      MeromorphicOn.divisor_apply hf.meromorphicOn (hsub hz)]
  · rw [MeromorphicOn.divisor_def]
    simp only [hz, and_false, ↓reduceIte]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z

/-- The common inner disk is independent of the moving sample point.
No fixed-center nonvanishing assumption is needed. -/
theorem moving_center_divisor_mass_le {f : ℂ → ℂ} {c a : ℂ} {r q B C : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hB : 0 ≤ B)
    (ha : a ∈ closedBall c r)
    (hf : AnalyticOnNhd ℂ f (closedBall c (5 * r)))
    (hupper : ∀ z ∈ closedBall c (5 * r), ‖f z‖ ≤ Real.exp (q * B))
    (hlower : Real.exp (-q * C) ≤ ‖f a‖) :
    ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c (2 * r)) z : ℤ) : ℝ) / q ≤
      (B + C) / Real.log (4 / 3 : ℝ) := by
  have hac : dist a c ≤ r := mem_closedBall.mp ha
  have hca : dist c a ≤ r := by simpa only [dist_comm] using hac
  have h4 : closedBall a (4 * r) ⊆ closedBall c (5 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have h3 : closedBall a (3 * r) ⊆ closedBall a (4 * r) :=
    closedBall_subset_closedBall (by linarith)
  have h2 : closedBall c (2 * r) ⊆ closedBall a (3 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have hm := divisor_sum_mono h2 (hf.mono (h3.trans h4))
  have hm' : ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c (2 * r)) z : ℤ) : ℝ) / q ≤
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall a (3 * r)) z : ℤ) : ℝ) / q := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hq.le
  have hJ := ScalarCompactnessJensen.normalized_divisor_mass_le
    (by linarith : 0 < 3 * r) (by linarith : 3 * r < 4 * r) hq hB (hf.mono h4)
    (fun z hz => hupper z (h4 (sphere_subset_closedBall hz))) hlower
  have he : 4 * r / (3 * r) = (4 / 3 : ℝ) := by field_simp
  rw [he] at hJ
  exact hm'.trans hJ

/-- Uniform L¹ bounds on a common disk from moving Cauchy sample points. -/
theorem moving_center_log_L1_bound {f : ℂ → ℂ} {c a : ℂ} {r q B C : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hB : 0 ≤ B)
    (ha : a ∈ closedBall c r)
    (hf : AnalyticOnNhd ℂ f (closedBall c (5 * r)))
    (hupper : ∀ z ∈ closedBall c (5 * r), ‖f z‖ ≤ Real.exp (q * B))
    (hlower : Real.exp (-q * C) ≤ ‖f a‖) :
    (∫ z in closedBall c (2 * r), |Real.log ‖f z‖ / q|) ≤
      (2 * B + C) * (Real.pi * (4 * r) ^ 2) := by
  have hac : dist a c ≤ r := mem_closedBall.mp ha
  have hca : dist c a ≤ r := by simpa only [dist_comm] using hac
  have h4 : closedBall a (4 * r) ⊆ closedBall c (5 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have h2 : closedBall c (2 * r) ⊆ closedBall a (4 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have ha0 : f a ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hlower)
  have hi := (ScalarCompactnessL1Bounds.log_inputs_on_disk
    (by positivity : 0 ≤ 4 * r) (hf.mono h4) ha0).1
  have hm : (∫ z in closedBall c (2 * r), |Real.log ‖f z‖ / q|) ≤
      ∫ z in closedBall a (4 * r), |Real.log ‖f z‖ / q| :=
    setIntegral_mono_set (hi.div_const q).abs (ae_of_all _ fun _ => abs_nonneg _)
      (ae_of_all _ fun _ hz => h2 hz)
  have hb := ScalarCompactnessL1Bounds.normalized_log_integral_abs_le
    (by positivity : 0 < 4 * r) hq hB (hf.mono h4) (fun z hz => hupper z (h4 hz)) hlower
  rw [Complex.volume_closedBall' (by positivity : 0 ≤ 4 * r)] at hb
  exact hm.trans hb

/-- Genuine common-disk divisor compactness from a moving analytic lower
sample. The mass bound is obtained internally from Jensen's formula. -/
theorem moving_center_divisor_potential_tendsto_subseq
    {f : ℕ → ℂ → ℂ} {q : ℕ → ℝ} {a : ℕ → ℂ} {c : ℂ} {r B C cutoff : ℝ}
    (hr : 0 < r) (hq : ∀ n, 0 < q n) (hB : 0 ≤ B)
    (ha : ∀ n, a n ∈ closedBall c r)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c (5 * r)))
    (hupper : ∀ n z, z ∈ closedBall c (5 * r) → ‖f n z‖ ≤ Real.exp (q n * B))
    (hlower : ∀ n, Real.exp (-q n * C) ≤ ‖f n (a n)‖) :
    ∃ u : ScalarCompactnessLogPotential.L1, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => ScalarCompactnessDivisor.divisorPotential
        (f (σ n)) c (2 * r) (q (σ n)) cutoff) atTop (𝓝 u) := by
  classical
  let M : ℝ := 1 + max 0 ((B + C) / Real.log (4 / 3 : ℝ))
  apply ScalarCompactnessDivisor.divisor_potential_tendsto_subseq_of_mass_bound hq
    (show 0 < M by dsimp [M]; positivity)
    (fun n => (hf n).mono (closedBall_subset_closedBall (by linarith)))
  intro n
  have hm := moving_center_divisor_mass_le hr (hq n) hB (ha n) (hf n) (hupper n) (hlower n)
  rw [ScalarCompactnessDivisor.divisor_sum_eq, Int.cast_sum, Finset.sum_div] at hm
  exact hm.trans (by dsimp [M]; linarith [le_max_right 0 ((B + C) / Real.log (4 / 3 : ℝ))])

#print axioms divisor_sum_mono
#print axioms moving_center_divisor_mass_le
#print axioms moving_center_log_L1_bound
#print axioms moving_center_divisor_potential_tendsto_subseq
end V10.ScalarCompactnessMovingCenter
