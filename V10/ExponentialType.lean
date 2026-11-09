import V10.ContinuousFrequency
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Literal extended-real exponential type

Both closed-disk and circle maximum moduli are actual suprema of |f|.
For continuous f and nonnegative radius they are finite and attained. The
maximum modulus principle proves equality for entire f at positive radii.
The paper's circle-based order-one type is an EReal limsup of log⁺ M(r,f) / r,
so infinite type is retained rather than collapsed by a real-valued limsup.
Only positive radii matter to the limit. The zero function has type zero.
-/

namespace V10.ExponentialType
open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section

/-- Actual closed-disk maximum modulus; continuity guarantees boundedness. -/
def diskMax (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' closedBall (0 : ℂ) r)

/-- Nonnegative logarithm, with value zero at zero. -/
def logPlus (x : ℝ) : ℝ := Real.log (max 1 x)

/-- The disk-based order-one type, with possible value +∞. Division at nonpositive
radii is immaterial because the limiting filter is r → +∞. -/
def typeOne (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ => ((logPlus (diskMax f r) / r : ℝ) : EReal)) atTop

lemma disk_norm_image_bddAbove {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    BddAbove ((fun z => ‖f z‖) '' closedBall (0 : ℂ) r) :=
  ((isCompact_closedBall (0 : ℂ) r).image (continuous_norm.comp hf)).bddAbove

lemma disk_norm_image_nonempty {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    ((fun z => ‖f z‖) '' closedBall (0 : ℂ) r).Nonempty :=
  (nonempty_closedBall.mpr hr).image _

/-- The supremum is an attained finite maximum, not a formal unbounded supremum. -/
theorem diskMax_attained {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ closedBall (0 : ℂ) r, diskMax f r = ‖f z‖ :=
  (isCompact_closedBall (0 : ℂ) r).exists_sSup_image_eq
    (nonempty_closedBall.mpr hr) (continuous_norm.comp hf).continuousOn

lemma norm_le_diskMax {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) : ‖f z‖ ≤ diskMax f r :=
  le_csSup (disk_norm_image_bddAbove hf r) (mem_image_of_mem _ hz)

lemma diskMax_nonneg {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ diskMax f r :=
  (norm_nonneg (f 0)).trans (norm_le_diskMax hf (mem_closedBall_self hr))

lemma diskMax_le {f : ℂ → ℂ} {r B : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ B) : diskMax f r ≤ B := by
  apply csSup_le (disk_norm_image_nonempty hr)
  rintro _ ⟨z, hz, rfl⟩
  exact hbound z hz

lemma logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x :=
  Real.log_nonneg (le_max_left 1 x)

lemma logPlus_zero : logPlus 0 = 0 := by simp [logPlus]

/-- The extended-real type cannot be negative because log⁺ is nonnegative
at every positive radius. No bounded-type premise is needed. -/
theorem typeOne_nonneg (f : ℂ → ℂ) : 0 ≤ typeOne f := by
  rw [← limsup_const (f := (atTop : Filter ℝ)) (0 : EReal)]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact_mod_cast div_nonneg (logPlus_nonneg (diskMax f r)) hr.le

/-- The zero function is handled explicitly, including log⁺(0)=0. -/
theorem typeOne_zero : typeOne (fun _ : ℂ => 0) = 0 := by
  have hm : ∀ r : ℝ, 0 ≤ r → diskMax (fun _ : ℂ => 0) r = 0 := by
    intro r hr
    apply le_antisymm (diskMax_le hr (by simp))
    exact diskMax_nonneg continuous_const hr
  unfold typeOne
  have heq : (fun r : ℝ => ((logPlus (diskMax (fun _ : ℂ => 0) r) / r : ℝ) : EReal))
      =ᶠ[atTop] (fun _ : ℝ => (0 : EReal)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp [hm r hr, logPlus_zero]
  rw [limsup_congr heq]
  exact limsup_const 0

/-- The actual maximum modulus inherits the global exponential bound. -/
theorem diskMax_le_exponential {f : ℂ → ℂ} {C σ r : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hr : 0 ≤ r)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖)) :
    diskMax f r ≤ C * Real.exp (σ * r) := by
  apply diskMax_le hr
  intro z hz
  have hzr : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  exact (hbound z).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzr hσ)) hC)

/-- A pointwise bound for the logarithmic growth profile. The constant max(1,C)
handles C=0 and small masses without taking the logarithm of a nonpositive number. -/
theorem logPlus_diskMax_div_le {f : ℂ → ℂ} {C σ r : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖)) :
    logPlus (diskMax f r) / r ≤ σ + Real.log (max 1 C) / r := by
  have hD : 0 < max 1 C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hExp : 1 ≤ Real.exp (σ * r) := Real.one_le_exp_iff.mpr (mul_nonneg hσ hr.le)
  have hM : diskMax f r ≤ max 1 C * Real.exp (σ * r) :=
    (diskMax_le_exponential hC hσ hr.le hbound).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hOne : 1 ≤ max 1 C * Real.exp (σ * r) := by
    nlinarith [le_max_left (1 : ℝ) C]
  have hmax := max_le hOne hM
  have hlog : logPlus (diskMax f r) ≤ Real.log (max 1 C) + σ * r := by
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 (diskMax f r))) hmax
    rwa [Real.log_mul (ne_of_gt hD) (Real.exp_ne_zero _), Real.log_exp] at hh
  calc
    logPlus (diskMax f r) / r ≤ (Real.log (max 1 C) + σ * r) / r :=
      div_le_div_of_nonneg_right hlog hr.le
    _ = σ + Real.log (max 1 C) / r := by field_simp; ring

/-- A genuine disk-based EReal-limsup bound from a global exponential estimate.
Continuity ensures that diskMax is the actual finite maximum modulus. -/
theorem typeOne_le_of_global_bound {f : ℂ → ℂ} (hf : Continuous f) {C σ : ℝ}
    (hσ : 0 ≤ σ) (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖)) :
    typeOne f ≤ (σ : EReal) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg (f 0)).trans (hbound 0)
    simpa using h
  have hfinite := disk_norm_image_bddAbove hf
  have hlimit : Tendsto (fun r : ℝ => σ + Real.log (max 1 C) / r)
      atTop (𝓝 σ) := by
    simpa using (tendsto_const_nhds (x := σ)).add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop))
  have hE : Tendsto (fun r : ℝ => ((σ + Real.log (max 1 C) / r : ℝ) : EReal))
      atTop (𝓝 (σ : EReal)) := EReal.tendsto_coe.mpr hlimit
  rw [← hE.limsup_eq]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact_mod_cast logPlus_diskMax_div_le hC hσ hr hbound

/-- For an entire function the literal type is finite under the global estimate. -/
theorem typeOne_finite_of_global_bound {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖)) :
    0 ≤ typeOne f ∧ typeOne f ≤ (σ : EReal) ∧ typeOne f ≠ ⊤ := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun z =>
    (hf z (mem_univ z)).continuousAt
  have hu := typeOne_le_of_global_bound hcont hσ hbound
  exact ⟨typeOne_nonneg f, hu, ne_top_of_le_ne_top (EReal.coe_ne_top σ) hu⟩

/-- Disk-based type at the exact compact frequency radius. The circle-based
manuscript type is identified with this value below. -/
theorem compact_frequency_typeOne_le (ν : ComplexMeasure ℂ)
    [IsFiniteMeasure ν.variation] {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hsupp : ν.variation Kᶜ = 0) :
    typeOne (ContinuousFrequency.complexTransform ν) ≤
      (ContinuousFrequency.frequencyRadius K : EReal) := by
  obtain ⟨ha, hb⟩ := ContinuousFrequency.compact_frequency_analytic_input ν hK hne hsupp
  exact (typeOne_finite_of_global_bound ha
    (ContinuousFrequency.frequencyRadius_nonneg hK hne) hb).2.1

/-- Actual maximum modulus on the circle used in the manuscript. -/
def sphereMax (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere (0 : ℂ) r)

/-- The literal manuscript type τ₁(f), with circle maximum modulus and an
extended-real limsup. -/
def typeOneSphere (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ => ((logPlus (sphereMax f r) / r : ℝ) : EReal)) atTop

lemma sphere_norm_image_bddAbove {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    BddAbove ((fun z => ‖f z‖) '' sphere (0 : ℂ) r) :=
  ((isCompact_sphere (0 : ℂ) r).image (continuous_norm.comp hf)).bddAbove

lemma sphere_norm_image_nonempty {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    ((fun z => ‖f z‖) '' sphere (0 : ℂ) r).Nonempty :=
  (NormedSpace.sphere_nonempty.mpr hr).image _

/-- Circle maximum modulus is finite and attained for continuous functions. -/
theorem sphereMax_attained {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ sphere (0 : ℂ) r, sphereMax f r = ‖f z‖ :=
  (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq
    (NormedSpace.sphere_nonempty.mpr hr) (continuous_norm.comp hf).continuousOn

lemma norm_le_sphereMax {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) r) : ‖f z‖ ≤ sphereMax f r :=
  le_csSup (sphere_norm_image_bddAbove hf r) (mem_image_of_mem _ hz)

/-- The actual disk and circle maxima agree for entire functions, by the
maximum modulus principle. This closes the difference in the two definitions. -/
theorem diskMax_eq_sphereMax {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {r : ℝ} (hr : 0 < r) : diskMax f r = sphereMax f r := by
  have hd : Differentiable ℂ f := Complex.analyticOnNhd_univ_iff_differentiable.mp hf
  apply le_antisymm
  · apply diskMax_le hr.le
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
      hd.diffContOnCl (fun w hw => norm_le_sphereMax hd.continuous
        (frontier_closedBall_subset_sphere hw))
    exact subset_closure hz
  · apply csSup_le (sphere_norm_image_nonempty hr.le)
    rintro _ ⟨z, hz, rfl⟩
    exact norm_le_diskMax hd.continuous (sphere_subset_closedBall hz)

/-- For entire functions the EReal disk type is exactly the manuscript's
circle-based EReal type; no finiteness of either type is assumed. -/
theorem typeOneSphere_eq_typeOne {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    typeOneSphere f = typeOne f := by
  apply limsup_congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [diskMax_eq_sphereMax hf hr]

theorem typeOneSphere_nonneg (f : ℂ → ℂ) : 0 ≤ typeOneSphere f := by
  rw [← limsup_const (f := (atTop : Filter ℝ)) (0 : EReal)]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact_mod_cast div_nonneg (logPlus_nonneg (sphereMax f r)) hr.le

theorem typeOneSphere_zero : typeOneSphere (fun _ : ℂ => 0) = 0 := by
  rw [typeOneSphere_eq_typeOne (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) univ)]
  exact typeOne_zero

/-- Literal τ₁(f) ≤ σ from a global exponential bound for an entire function. -/
theorem typeOneSphere_le_of_global_bound {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {C σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖)) :
    typeOneSphere f ≤ (σ : EReal) := by
  rw [typeOneSphere_eq_typeOne hf]
  exact (typeOne_finite_of_global_bound hf hσ hbound).2.1

/-- The literal circle-based exponential-type conclusion in Corollary 7.5. -/
theorem compact_frequency_typeOneSphere_le (ν : ComplexMeasure ℂ)
    [IsFiniteMeasure ν.variation] {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hsupp : ν.variation Kᶜ = 0) :
    typeOneSphere (ContinuousFrequency.complexTransform ν) ≤
      (ContinuousFrequency.frequencyRadius K : EReal) := by
  obtain ⟨ha, hb⟩ := ContinuousFrequency.compact_frequency_analytic_input ν hK hne hsupp
  exact typeOneSphere_le_of_global_bound ha
    (ContinuousFrequency.frequencyRadius_nonneg hK hne) hb

/-- Growth to infinity produces actual extended-real infinite type. -/
theorem typeOneSphere_eq_top_of_growth {f : ℂ → ℂ}
    (hgrowth : Tendsto (fun r : ℝ => logPlus (sphereMax f r) / r) atTop atTop) :
    typeOneSphere f = ⊤ := by
  exact (EReal.tendsto_coe_atTop.comp hgrowth).limsup_eq

#print axioms diskMax_attained
#print axioms typeOne_zero
#print axioms typeOne_le_of_global_bound
#print axioms typeOne_finite_of_global_bound
#print axioms compact_frequency_typeOne_le
#print axioms sphereMax_attained
#print axioms diskMax_eq_sphereMax
#print axioms typeOneSphere_eq_typeOne
#print axioms typeOneSphere_zero
#print axioms typeOneSphere_le_of_global_bound
#print axioms compact_frequency_typeOneSphere_le
#print axioms typeOneSphere_eq_top_of_growth
end
end V10.ExponentialType
