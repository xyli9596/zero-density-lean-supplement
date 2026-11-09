module
public import Ray.Hartogs.Subharmonic
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
import all Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-!
# Interior compactness from actual harmonicity and an L¹ bound

The analytic input is mathlib's `InnerProductSpace.HarmonicOnNhd`, not an
assumed equicontinuity property. Disk submeans give interior uniform bounds;
the Poisson formula gives a common Lipschitz bound on smaller disks.
-/

public section
noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology Real NNReal BoundedContinuousFunction

namespace V10.HarmonicL1Compactness
set_option backward.isDefEq.respectTransparency false

theorem circleAverage_eq_ray_mean (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r = ⨍ t in itau, f (circleMap c r t) := by
  rw [Real.circleAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply,
    Set.univ_inter, itau_real_volume]
  rfl

theorem harmonicOnNhd_to_ray {f : ℂ → ℝ} {s : Set ℂ}
    (hf : InnerProductSpace.HarmonicOnNhd f s) : HarmonicOn f s := by
  refine ⟨hf.continuousOn, ?_⟩
  intro c r hr hsub
  rw [← circleAverage_eq_ray_mean]
  exact ((hf.mono (by simpa [abs_of_pos hr] using hsub)).circleAverage_eq).symm

/-- The genuine harmonic submean estimate, including the actual area factor. -/
theorem norm_le_disk_L1 {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c r)) (hr : 0 < r) :
    ‖f c‖ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in closedBall c r, ‖f z‖ := by
  have h := (harmonicOnNhd_to_ray hf).norm.submean_disk hr
  simpa only [average_eq, MeasurableSet.univ, measureReal_restrict_apply,
    Set.univ_inter, Complex.volume_closedBall' hr.le, smul_eq_mul] using h

/-- A larger-disk L¹ bound controls every point of a smaller concentric disk. -/
theorem norm_le_of_disk_L1 {f : ℂ → ℝ} {c z : ℂ} {r R M : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c R))
    (hrR : r < R) (hz : z ∈ closedBall c r)
    (hM : (∫ w in closedBall c R, ‖f w‖) ≤ M) :
    ‖f z‖ ≤ (Real.pi * (R - r) ^ 2)⁻¹ * M := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hsub : closedBall z (R - r) ⊆ closedBall c R := by
    intro w hw
    apply mem_closedBall.mpr
    calc
      dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
      _ ≤ (R - r) + r := add_le_add (mem_closedBall.mp hw) (mem_closedBall.mp hz)
      _ = R := sub_add_cancel _ _
  have hi : IntegrableOn (fun w => ‖f w‖) (closedBall c R) :=
    hf.continuousOn.norm.integrableOn_compact (isCompact_closedBall c R)
  have hm : (∫ w in closedBall z (R - r), ‖f w‖) ≤ M := by
    apply le_trans ?_ hM
    exact setIntegral_mono_set hi (by filter_upwards with w using norm_nonneg (f w))
      (Filter.Eventually.of_forall hsub)
  exact (norm_le_disk_L1 (hf.mono hsub) hd).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The pole variable of the Poisson kernel has a uniform Lipschitz bound
on every strictly smaller disk. -/
theorem herglotz_kernel_sub_bound {c z x y : ℂ} {r R : ℝ}
    (hrR : r < R) (hz : z ∈ sphere c R)
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖herglotzRieszKernel c x z - herglotzRieszKernel c y z‖ ≤
      (2 * R / (R - r) ^ 2) * ‖x - y‖ := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hz' : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have hx' : ‖x - c‖ ≤ r := mem_closedBall_iff_norm.mp hx
  have hy' : ‖y - c‖ ≤ r := mem_closedBall_iff_norm.mp hy
  have hdx : R - r ≤ ‖z - x‖ := by
    have ht := norm_add_le (z - x) (x - c)
    rw [sub_add_sub_cancel, hz'] at ht
    linarith
  have hdy : R - r ≤ ‖z - y‖ := by
    have ht := norm_add_le (z - y) (y - c)
    rw [sub_add_sub_cancel, hz'] at ht
    linarith
  have hnx : z - x ≠ 0 := norm_pos_iff.mp (hd.trans_le hdx)
  have hny : z - y ≠ 0 := norm_pos_iff.mp (hd.trans_le hdy)
  have he : herglotzRieszKernel c x z - herglotzRieszKernel c y z =
      2 * (z - c) * (x - y) / ((z - x) * (z - y)) := by
    simp only [herglotzRieszKernel_def, sub_sub_sub_cancel_right]
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_mul, norm_mul, hz']
  norm_num only [Complex.norm_ofNat]
  have hR : 0 ≤ R := hz' ▸ norm_nonneg (z - c)
  have hden : (R - r) ^ 2 ≤ ‖z - x‖ * ‖z - y‖ := by
    nlinarith [mul_le_mul hdx hdy hd.le (norm_nonneg (z - x))]
  calc
    2 * R * ‖x - y‖ / (‖z - x‖ * ‖z - y‖) ≤
        2 * R * ‖x - y‖ / (R - r) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd) hden
    _ = (2 * R / (R - r) ^ 2) * ‖x - y‖ := by ring

/-- Actual Poisson representation transfers the kernel estimate to a harmonic
function; the only bound assumed here is on the enclosing circle. -/
theorem harmonic_sub_bound_of_circle_bound {f : ℂ → ℝ} {c x y : ℂ} {r R B : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c R))
    (hr : 0 ≤ r) (hrR : r < R) (_hB : 0 ≤ B)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ B)
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖f x - f y‖ ≤ (2 * R / (R - r) ^ 2 * B) * ‖x - y‖ := by
  have hR : 0 < R := hr.trans_lt hrR
  have hxb : x ∈ ball c R := closedBall_subset_ball hrR hx
  have hyb : y ∈ ball c R := closedBall_subset_ball hrR hy
  let k : ℂ → ℂ → ℝ := fun w z => (herglotzRieszKernel c w z).re * f z
  have hc (w : ℂ) (hw : w ∈ ball c R) : ContinuousOn (k w) (sphere c R) := by
    have hk : ContinuousOn (herglotzRieszKernel c w) (sphere c R) := by
      simpa [abs_of_pos hR] using continuousOn_herglotzRieszKernel_sphere hw
    exact (Complex.continuous_re.comp_continuousOn hk).mul
      (hf.continuousOn.mono sphere_subset_closedBall)
  have hix : CircleIntegrable (k x) c R := ContinuousOn.circleIntegrable' (by simpa [abs_of_pos hR] using hc x hxb)
  have hiy : CircleIntegrable (k y) c R := ContinuousOn.circleIntegrable' (by simpa [abs_of_pos hR] using hc y hyb)
  have hpx : Real.circleAverage (k x) c R = f x := by
    exact hf.circleAverage_re_herglotzRieszKernel_smul hxb
  have hpy : Real.circleAverage (k y) c R = f y := by
    exact hf.circleAverage_re_herglotzRieszKernel_smul hyb
  rw [← hpx, ← hpy, ← Real.circleAverage_sub hix hiy, Real.norm_eq_abs]
  apply (Real.abs_circleAverage_le_circleAverage_abs).trans
  apply Real.circleAverage_mono_on_of_le_circle (hix.sub hiy).abs
  intro z hz
  have hzR : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
  have hk : |(herglotzRieszKernel c x z).re -
      (herglotzRieszKernel c y z).re| ≤
      (2 * R / (R - r) ^ 2) * ‖x - y‖ := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (herglotz_kernel_sub_bound hrR hzR hx hy)
  have hcoef : 0 ≤ 2 * R / (R - r) ^ 2 := by positivity
  change |k x z - k y z| ≤ _
  dsimp [k]
  rw [← sub_mul, abs_mul]
  calc
    _ ≤ ((2 * R / (R - r) ^ 2) * ‖x - y‖) * B :=
      mul_le_mul hk (by simpa only [Real.norm_eq_abs] using hb z hzR) (abs_nonneg _) (by positivity)
    _ = (2 * R / (R - r) ^ 2 * B) * ‖x - y‖ := by ring

/-- A common L¹ bound for genuinely harmonic functions supplies both uniform
boundedness and a common Lipschitz constant on an interior disk. -/
theorem harmonic_L1_common_bounds {h : ℕ → ℂ → ℝ} {c : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hh : ∀ n, InnerProductSpace.HarmonicOnNhd (h n) (closedBall c R))
    (hM : ∀ n, (∫ z in closedBall c R, ‖h n z‖) ≤ M) :
    ∃ B C : ℝ≥0, (∀ n z, z ∈ closedBall c r → ‖h n z‖ ≤ B) ∧
      ∀ n, LipschitzOnWith C (h n) (closedBall c r) := by
  let ρ := (R + r) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have hM0 : 0 ≤ M := (integral_nonneg fun z => norm_nonneg (h 0 z)).trans (hM 0)
  let B : ℝ≥0 := ⟨(Real.pi * (R - ρ) ^ 2)⁻¹ * M, by positivity⟩
  let C : ℝ≥0 := ⟨2 * ρ / (ρ - r) ^ 2 * B, by positivity⟩
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ closedBall c ρ) : ‖h n z‖ ≤ B :=
    norm_le_of_disk_L1 (hh n) hρR hz (hM n)
  refine ⟨B, C, ?_, ?_⟩
  · intro n z hz
    exact hb n z (closedBall_subset_closedBall hrρ.le hz)
  · intro n
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    change ‖h n x - h n y‖ ≤ (2 * ρ / (ρ - r) ^ 2 * B) * ‖x - y‖
    exact harmonic_sub_bound_of_circle_bound ((hh n).mono (closedBall_subset_closedBall hρR.le))
        hr hrρ B.coe_nonneg (fun z hz => hb n z (sphere_subset_closedBall hz)) hx hy

/-- Interior uniform subsequence compactness derived from actual harmonicity
and an actual area L¹ bound. No equicontinuity, compact range, or convergent
subsequence is an input. -/
theorem harmonic_L1_uniform_subsequence {h : ℕ → ℂ → ℝ} {c : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hh : ∀ n, InnerProductSpace.HarmonicOnNhd (h n) (closedBall c R))
    (hM : ∀ n, (∫ z in closedBall c R, ‖h n z‖) ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : ℂ → ℝ,
      ContinuousOn g (closedBall c r) ∧
      TendstoUniformlyOn (fun n => h (σ n)) g atTop (closedBall c r) := by
  classical
  obtain ⟨B, C, hb, hLip⟩ := harmonic_L1_common_bounds hr hrR hh hM
  let K := closedBall c r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  let F : ℕ → K →ᵇ ℝ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => h n x, continuousOn_iff_continuous_domRestrict.mp (hLip n).continuousOn⟩
  have heq : Equicontinuous ((↑) : range F → K → ℝ) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => (C : ℝ) * t)
      (by simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).const_mul (C : ℝ)))
    intro x y f
    obtain ⟨n, hn⟩ := f.property
    simpa only [← hn, F, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      Subtype.dist_eq]
      using (hLip n).dist_le_mul x x.property y y.property
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) B)
      (isCompact_closedBall _ _) (range F) (by
        intro f x hf
        obtain ⟨n, rfl⟩ := hf
        simpa only [F, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
          mem_closedBall, dist_zero_right] using hb n x x.property) heq
  obtain ⟨a, _, σ, hσ, ha⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let g : ℂ → ℝ := fun z => if hz : z ∈ K then a ⟨z, hz⟩ else 0
  have hg_eq : K.domRestrict g = (a : K → ℝ) := by
    funext x
    simp only [Set.domRestrict_apply, g, dif_pos x.property]
  have hg : ContinuousOn g K := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    rw [hg_eq]
    exact a.continuous
  refine ⟨σ, hσ, g, hg, ?_⟩
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ha
  change TendstoUniformly (fun n (x : K) => h (σ n) x) (K.domRestrict g) atTop
  rw [hg_eq]
  exact hu

#print axioms norm_le_of_disk_L1
#print axioms harmonic_L1_common_bounds
#print axioms harmonic_L1_uniform_subsequence

end V10.HarmonicL1Compactness
