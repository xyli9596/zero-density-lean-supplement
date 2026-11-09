import V10.ScalarL1Hartogs
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Ball averages of an L¹ limit

These lemmas allow scalar-limit identification using an arbitrary L¹
representative. No upper-semicontinuous representative is assumed: moving
disk integrals are continuous by dominated convergence, and Lebesgue
differentiation converts disk-average inequalities into almost-everywhere
point inequalities.
-/

noncomputable section
open Filter MeasureTheory Set Metric
open scoped Topology
namespace V10.ScalarL1IdentificationAverage
set_option backward.isDefEq.respectTransparency false

/-- Translation of the center of a disk is continuous for every genuine L¹
integrand. Its possible pointwise discontinuities lie on a null circle. -/
theorem continuousAt_disk_integral {g : ℂ → ℝ} (hg : Integrable g volume)
    (x : ℂ) (r : ℝ) :
    ContinuousAt (fun z => ∫ w in closedBall z r, g w) x := by
  have ht : Tendsto (fun z => ∫ w, (closedBall z r).indicator g w)
      (𝓝 x) (𝓝 (∫ w, (closedBall x r).indicator g w)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun w => ‖g w‖)
    · exact Eventually.of_forall fun z => (hg.indicator measurableSet_closedBall).aestronglyMeasurable
    · exact Eventually.of_forall fun z => ae_of_all _ fun w =>
        norm_indicator_le_norm_self _ _
    · exact hg.norm
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume x r)] with w hw
      change dist w x ≠ r at hw
      have hc : ContinuousAt (fun z : ℂ => dist w z) x := continuousAt_const.dist continuousAt_id
      by_cases hin : w ∈ closedBall x r
      · have hlt : dist w x < r := lt_of_le_of_ne (mem_closedBall.mp hin)
          hw
        have he : ∀ᶠ z in 𝓝 x, w ∈ closedBall z r :=
          (hc.eventually (gt_mem_nhds hlt)).mono fun z hz => mem_closedBall.mpr hz.le
        have heq : (fun z => (closedBall z r).indicator g w) =ᶠ[𝓝 x] fun _ => g w :=
          he.mono fun z hz => indicator_of_mem hz g
        rw [indicator_of_mem hin]
        exact tendsto_const_nhds.congr' heq.symm
      · have hgt : r < dist w x := lt_of_not_ge (by simpa only [mem_closedBall] using hin)
        have he : ∀ᶠ z in 𝓝 x, w ∉ closedBall z r :=
          (hc.eventually (lt_mem_nhds hgt)).mono fun z hz => by
            simpa only [mem_closedBall, not_le] using hz
        have heq : (fun z => (closedBall z r).indicator g w) =ᶠ[𝓝 x] fun _ => 0 :=
          he.mono fun z hz => indicator_of_notMem hz g
        rw [indicator_of_notMem hin]
        exact tendsto_const_nhds.congr' heq.symm
  simpa only [ContinuousAt, integral_indicator measurableSet_closedBall] using ht

theorem continuousAt_disk_average {g : ℂ → ℝ} (hg : Integrable g volume)
    (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ContinuousAt (fun z => ⨍ w in closedBall z r, g w) x := by
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply,
    Set.univ_inter, Complex.volume_closedBall' hr, smul_eq_mul]
  exact continuousAt_const.mul (continuousAt_disk_integral hg x r)

/-- The normalized integral error is controlled on a single larger set,
uniformly in every disk center for which the disk fits in that set. -/
theorem disk_average_le_average_add_L1 {u g : ℂ → ℝ} {D : Set ℂ}
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hsub : closedBall x r ⊆ D)
    (hu : IntegrableOn u D) (hg : IntegrableOn g D) :
    (⨍ z in closedBall x r, u z) ≤ (⨍ z in closedBall x r, g z) +
      (Real.pi * r ^ 2)⁻¹ * ∫ z in D, ‖u z - g z‖ := by
  have hi : (∫ z in closedBall x r, u z - g z) ≤ ∫ z in D, ‖u z - g z‖ := by
    calc
      _ ≤ ∫ z in closedBall x r, ‖u z - g z‖ :=
        integral_mono_ae ((hu.mono_set hsub).sub (hg.mono_set hsub))
          (((hu.mono_set hsub).sub (hg.mono_set hsub)).norm)
          (ae_of_all _ fun z => le_abs_self (u z - g z))
      _ ≤ ∫ z in D, ‖u z - g z‖ :=
        setIntegral_mono_set (hu.sub hg).norm (ae_of_all _ fun z => norm_nonneg _)
          (ae_of_all _ fun z hz => hsub hz)
  rw [integral_sub (hu.mono_set hsub) (hg.mono_set hsub)] at hi
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply,
    Set.univ_inter, Complex.volume_closedBall' hr.le, smul_eq_mul]
  have hp : 0 ≤ (Real.pi * r ^ 2)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hi hp]

/-- Lebesgue differentiation closes a disk-average lower comparison. -/
theorem ae_le_of_eventually_le_disk_average {g H : ℂ → ℝ} {D : Set ℂ}
    (hD : MeasurableSet D) (hg : Integrable g volume)
    (hle : ∀ x ∈ D, ∀ᶠ r in 𝓝[>] (0 : ℝ), H x ≤ ⨍ z in closedBall x r, g z) :
    ∀ᵐ x ∂volume.restrict D, H x ≤ g x := by
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable (1 : ℝ)
  filter_upwards [ae_restrict_of_ae hLeb, ae_restrict_mem hD] with x hx hxD
  have hm : ∀ᶠ r in 𝓝[>] (0 : ℝ), x ∈ closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul] using mem_closedBall_self (le_of_lt hr)
  exact ge_of_tendsto (hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hm) (hle x hxD)

#print axioms continuousAt_disk_integral
#print axioms ae_le_of_eventually_le_disk_average
end V10.ScalarL1IdentificationAverage
