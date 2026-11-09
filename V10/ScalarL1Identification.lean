import V10.ScalarL1IdentificationAverage
import V10.ScalarCauchyNoncollapse
import V10.ScalarL1Convergence
import Mathlib.Tactic

/-!
# Identification of scalar L¹ subsequence limits with the actual jet limit

The lower comparison uses Cauchy samples of the actual analytic function,
disk submeans, continuity of L¹ disk averages, and Lebesgue differentiation.
It does not assume a subharmonic or upper-semicontinuous representative of
the L¹ limit, nor pointwise convergence of scalar logarithms.
-/

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology
namespace V10.ScalarL1Identification
set_option backward.isDefEq.respectTransparency false

open ScalarL1IdentificationAverage

/-- Actual Cauchy samples and scalar L¹ convergence force the limiting jet
rate below every sufficiently interior disk average of the L¹ limit. -/
theorem jet_limit_le_disk_average {n : ℕ} {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn₀ : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    (hD : IsCompact D) {R : ℕ → ℝ} (hR : ∀ i, 1 ≤ R i)
    (hRt : Tendsto R atTop atTop)
    (hDS : ∀ i z, z ∈ D → (R i : ℂ) * z ∈ S)
    {g : ℂ → ℝ} (hg : Integrable g volume)
    (hL1 : Tendsto (fun i => ∫ z in D, ‖ScalarAnalytic.potential v (R i) z - g z‖)
      atTop (𝓝 0))
    {x : ℂ} {r L : ℝ} (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ D)
    (hjet : ∀ i, ZeroDensity.ScalarLimit.jet n v ((R i : ℂ) * x) ≠ 0)
    (hjetlim : Tendsto (fun i => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) (R i) x) atTop (𝓝 L)) :
    L ≤ ⨍ z in closedBall x r, g z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hcont := continuousAt_disk_average hg x hr.le
  obtain ⟨δ₀, hδ₀, hδavg⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (gt_mem_nhds (lt_add_of_pos_right (⨍ z in closedBall x r, g z) hε)))
  let δ := min r (δ₀ / 2)
  have hδ : 0 < δ := lt_min hr (half_pos hδ₀)
  have hδr : δ ≤ r := min_le_left _ _
  have hδδ₀ : δ < δ₀ := (min_le_right _ _).trans_lt (half_lt_self hδ₀)
  have hsmall : closedBall x δ ⊆ D :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  have hdisks (z : ℂ) (hz : z ∈ closedBall x δ) : closedBall z r ⊆ D := by
    apply subset_trans _ hball
    intro w hw
    apply mem_closedBall.mpr
    calc
      dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ ≤ r + δ := add_le_add (mem_closedBall.mp hw) (mem_closedBall.mp hz)
      _ ≤ 2 * r := by linarith
  have hRp (i : ℕ) : 0 < R i := zero_lt_one.trans_le (hR i)
  have hgerm := ScalarAnalytic.germs_ne_zero_of_jet hS hconn hv hz₀ hn₀
  have hA (i : ℕ) : AnalyticOnNhd ℂ (fun z => v ((R i : ℂ) * z)) D :=
    ScalarAnalytic.dilated_analyticOnNhd hv (hDS i)
  have hgn (i : ℕ) (z : ℂ) (hz : z ∈ D) :
      ¬(fun w => v ((R i : ℂ) * w)) =ᶠ[𝓝 z] 0 :=
    ScalarAnalytic.dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr (hRp i).ne')
      (hgerm _ (hDS i z hz))
  have hi (i : ℕ) : IntegrableOn (fun z => Real.log ‖v ((R i : ℂ) * z)‖) D :=
    (ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm (hA i) (hgn i)).integrableOn_isCompact hD
  have hae (i : ℕ) : ∀ᵐ z ∂volume.restrict D, v ((R i : ℂ) * z) ≠ 0 :=
    ScalarAnalytic.ae_ne_zero_of_germs hD.measurableSet (hA i) (hgn i)
  have hphysical (i : ℕ) : AnalyticOnNhd ℂ v
      (closedBall ((R i : ℂ) * x) (R i * δ)) := by
    apply hv.mono
    intro w hw
    have hz := hsmall (ScalarCauchyNoncollapse.rescaled_mem_closedBall (hRp i) hw)
    have hm := hDS i ((R i : ℂ)⁻¹ * w) hz
    simpa only [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hRp i).ne'), one_mul] using hm
  have hbound (i : ℕ) : PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) (R i) x -
        Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R i ≤
      (⨍ z in closedBall x r, g z) + ε + (Real.pi * r ^ 2)⁻¹ *
        ∫ z in D, ‖ScalarAnalytic.potential v (R i) z - g z‖ := by
    obtain ⟨z, hz, hzn, hsample⟩ := ScalarCauchyNoncollapse.exists_scalar_log_sample
      (hR i) hδ (hphysical i) (hjet i)
    have hs := ScalarLogSubmean.normalized_log_norm_le_disk_average hr (hRp i)
      ((hA i).mono (hdisks z hz)) hzn
      ((hae i).filter_mono (ae_mono (Measure.restrict_mono (hdisks z hz) le_rfl)))
      ((hi i).mono_set (hdisks z hz))
    have herr := disk_average_le_average_add_L1 hr (hdisks z hz)
      ((hi i).div_const (R i)) hg.integrableOn
    have havg : (⨍ w in closedBall z r, g w) ≤ (⨍ w in closedBall x r, g w) + ε :=
      (hδavg ((mem_closedBall.mp hz).trans_lt hδδ₀)).le
    apply hsample.trans (hs.trans (herr.trans ?_))
    dsimp only [ScalarAnalytic.potential]
    linarith
  have he : Tendsto (fun i => Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R i)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hRt
  have hleft : Tendsto (fun i => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) (R i) x -
        Real.log (ZeroDensity.ScalarLimit.cauchyConstant n δ) / R i) atTop (𝓝 L) := by
    simpa only [sub_zero] using hjetlim.sub he
  have hright : Tendsto (fun i => (⨍ z in closedBall x r, g z) + ε +
      (Real.pi * r ^ 2)⁻¹ * ∫ z in D, ‖ScalarAnalytic.potential v (R i) z - g z‖)
      atTop (𝓝 ((⨍ z in closedBall x r, g z) + ε)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hL1.const_mul (Real.pi * r ^ 2)⁻¹))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

/-- The difficult lower identification, for an arbitrary L¹ representative.
The zero extension is only an integration device; the conclusion concerns
the original representative on the interior of D. -/
theorem jet_limit_le_scalar_L1_limit_ae {n : ℕ} {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn₀ : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    (hD : IsCompact D) {R : ℕ → ℝ} (hR : ∀ i, 1 ≤ R i)
    (hRt : Tendsto R atTop atTop)
    (hDS : ∀ i z, z ∈ D → (R i : ℂ) * z ∈ S)
    {g H : ℂ → ℝ} (hg : IntegrableOn g D)
    (hL1 : Tendsto (fun i => ∫ z in D, ‖ScalarAnalytic.potential v (R i) z - g z‖)
      atTop (𝓝 0))
    (hjet : ∀ i x, x ∈ interior D → ZeroDensity.ScalarLimit.jet n v ((R i : ℂ) * x) ≠ 0)
    (hjetlim : ∀ x ∈ interior D, Tendsto (fun i => PerronVectorLimit.potential
      (ZeroDensity.ScalarLimit.jet n v) (R i) x) atTop (𝓝 (H x))) :
    ∀ᵐ x ∂volume.restrict (interior D), H x ≤ g x := by
  let G := D.indicator g
  have hG : Integrable G volume := (integrable_indicator_iff hD.measurableSet).mpr hg
  have hL1G : Tendsto (fun i => ∫ z in D, ‖ScalarAnalytic.potential v (R i) z - G z‖)
      atTop (𝓝 0) := by
    apply hL1.congr'
    apply Eventually.of_forall
    intro i
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
    simp only [G, indicator_of_mem hz]
  have hle : ∀ x ∈ interior D, ∀ᶠ r in 𝓝[>] (0 : ℝ), H x ≤ ⨍ z in closedBall x r, G z := by
    intro x hx
    obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    filter_upwards [Ioo_mem_nhdsGT (half_pos hε)] with r hr
    have hball : closedBall x (2 * r) ⊆ D :=
      (closedBall_subset_ball (by linarith [hr.2])).trans hεD
    exact jet_limit_le_disk_average hS hconn hv hz₀ hn₀ hD hR hRt hDS hG hL1G
      hr.1 hball (fun i => hjet i x hx) (hjetlim x hx)
  have hlower := ae_le_of_eventually_le_disk_average isOpen_interior.measurableSet hG hle
  filter_upwards [hlower, ae_restrict_mem isOpen_interior.measurableSet] with x hx hxD
  simpa only [G, indicator_of_mem (interior_subset hxD)] using hx

#print axioms jet_limit_le_disk_average
#print axioms jet_limit_le_scalar_L1_limit_ae
end V10.ScalarL1Identification
