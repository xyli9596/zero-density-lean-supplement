module
public import Ray.Hartogs.Subharmonic
public import V10.HarmonicL1Compactness
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Topology.Connected.Clopen
import all Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-!
# Convexity of homogeneous subharmonic functions in tangent coordinates

The maximum principle supplies the analytic step in local root selection.
No support inequality or convexity of the indicator is an input.
-/

public section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace V10.HomogeneousSubharmonicConvex
set_option backward.isDefEq.respectTransparency false

/-- The strong maximum principle on any open connected domain, obtained from
the proved disk maximum principle. -/
theorem eqOn_of_maximum {f : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : SubharmonicOn f D)
    {c : ℂ} (hc : c ∈ D) (hmax : ∀ z ∈ D, f z ≤ f c) :
    ∀ z ∈ D, f z = f c := by
  let E : Set D := {z | f z = f c}
  have hEc : IsClosed E := isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hf.cont)
    continuous_const
  have hEo : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds z.property)
    have hhalf : closedBall (z : ℂ) (r / 2) ⊆ D :=
      (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    have hz' : f z = f c := hz
    have he := (hf.mono hhalf).maximum_principle_ball (by linarith : 0 < r / 2)
      (show IsMaxOn f (closedBall (z : ℂ) (r / 2)) z from
        fun w hw => by change f w ≤ f z; rw [hz']; exact hmax w (hhalf hw))
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (closedBall_mem_nhds (z : ℂ) (by linarith : 0 < r / 2))] with w hw
    exact (he w hw).symm.trans hz
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hconn
  have hEu : E = univ := (show IsClopen E from ⟨hEc, hEo⟩).eq_univ ⟨⟨c, hc⟩, rfl⟩
  intro z hz
  have : (⟨z, hz⟩ : D) ∈ E := by rw [hEu]; trivial
  exact this

def tangentPoint (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

def tangentCone (S : Set ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.im / z.re ∈ S}

@[simp] theorem tangentPoint_re (t : ℝ) : (tangentPoint t).re = 1 := by
  simp [tangentPoint]

@[simp] theorem tangentPoint_im (t : ℝ) : (tangentPoint t).im = t := by
  simp [tangentPoint]

theorem tangentPoint_mem {S : Set ℝ} {t : ℝ} (ht : t ∈ S) :
    tangentPoint t ∈ tangentCone S := by simpa [tangentCone] using And.intro (zero_lt_one : (0:ℝ)<1) ht

theorem tangentCone_mono {S T : Set ℝ} (h : S ⊆ T) : tangentCone S ⊆ tangentCone T :=
  fun _ hz => ⟨hz.1, h hz.2⟩

theorem tangent_decomposition {z : ℂ} (hz : z.re ≠ 0) :
    z.re • tangentPoint (z.im / z.re) = z := by
  apply Complex.ext
  · simp [tangentPoint]
  · simp only [Complex.smul_im, tangentPoint_im, smul_eq_mul]
    field_simp

theorem tangentCone_Ioo {a b : ℝ} : tangentCone (Ioo a b) =
    {z : ℂ | 0 < z.re ∧ a * z.re < z.im ∧ z.im < b * z.re} := by
  ext z
  simp only [tangentCone, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨hz, ha, hb⟩
    exact ⟨hz, (lt_div_iff₀ hz).mp ha, (div_lt_iff₀ hz).mp hb⟩
  · rintro ⟨hz, ha, hb⟩
    exact ⟨hz, (lt_div_iff₀ hz).mpr ha, (div_lt_iff₀ hz).mpr hb⟩

theorem tangentCone_Ioo_isOpen (a b : ℝ) : IsOpen (tangentCone (Ioo a b)) := by
  rw [tangentCone_Ioo]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt (continuous_const.mul Complex.continuous_re) Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re)))

theorem tangentCone_Ioo_convex (a b : ℝ) : Convex ℝ (tangentCone (Ioo a b)) := by
  rw [tangentCone_Ioo]
  intro x hx y hy u v hu hv huv
  simp only [mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] at *
  have hpos : ∀ p q : ℝ, 0 < p → 0 < q → 0 < u * p + v * q := by
    intro p q hp hq
    rcases eq_or_lt_of_le hu with he | he
    · have hv1 : v = 1 := by linarith
      simp [← he, hv1, hq]
    · exact add_pos_of_pos_of_nonneg (mul_pos he hp) (mul_nonneg hv hq.le)
  constructor
  · exact hpos _ _ hx.1 hy.1
  · constructor
    · nlinarith [hpos (x.im - a * x.re) (y.im - a * y.re)
        (by linarith [hx.2.1]) (by linarith [hy.2.1])]
    · nlinarith [hpos (b * x.re - x.im) (b * y.re - y.im)
        (by linarith [hx.2.2]) (by linarith [hy.2.2])]

theorem continuous_tangentPoint : Continuous tangentPoint := by
  unfold tangentPoint
  fun_prop

/-- A linear function above the two endpoints of a tangent interval is above
the entire interval. Positive homogeneity turns a hypothetical interior
excess into an interior maximum of a genuinely subharmonic function. -/
theorem tangent_chord_majorant {H : ℂ → ℝ} {S : Set ℝ}
    (hH : SubharmonicOn H (tangentCone S))
    (hhom : ∀ r : ℝ, 0 < r → ∀ t ∈ S,
      H (r • tangentPoint t) = r * H (tangentPoint t))
    {a b A B : ℝ} (hab : a < b) (hI : Icc a b ⊆ S)
    (ha : H (tangentPoint a) ≤ A * a + B)
    (hb : H (tangentPoint b) ≤ A * b + B) :
    ∀ t ∈ Icc a b, H (tangentPoint t) ≤ A * t + B := by
  let g : ℝ → ℝ := fun t => H (tangentPoint t) - (A * t + B)
  have hg : ContinuousOn g (Icc a b) :=
    (hH.cont.comp continuous_tangentPoint.continuousOn
      (fun t ht => tangentPoint_mem (hI ht))).sub
        ((continuous_const.mul continuous_id).add continuous_const).continuousOn
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hg
  have ha' : g a ≤ 0 := by dsimp [g]; linarith
  have hb' : g b ≤ 0 := by dsimp [g]; linarith
  suffices hgc : g c ≤ 0 by
    intro t ht
    have := (hmax ht).trans hgc
    dsimp [g] at this
    linarith
  by_contra hbad
  have hgc : 0 < g c := lt_of_not_ge hbad
  have hcI : c ∈ Ioo a b := by
    constructor
    · have : c ≠ a := by intro h; subst c; linarith
      exact lt_of_le_of_ne hc.1 (Ne.symm this)
    · have : c ≠ b := by intro h; subst c; linarith
      exact lt_of_le_of_ne hc.2 this
  let F : ℂ → ℝ := fun z => H z - ((B + g c) * z.re + A * z.im)
  have hF : SubharmonicOn F (tangentCone (Ioo a b)) := by
    have han : AnalyticOnNhd ℂ (fun z : ℂ =>
        ((-(B + g c) : ℂ) + (A : ℂ) * Complex.I) * z) (tangentCone (Ioo a b)) := by
      intro z hz
      fun_prop
    have hs := (hH.mono (tangentCone_mono (Ioo_subset_Icc_self.trans hI))).add
      han.reSubharmonicOn
    convert hs using 1
    ext z
    simp [F, Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  have hFform : ∀ z ∈ tangentCone (Ioo a b),
      F z = z.re * (g (z.im / z.re) - g c) := by
    intro z hz
    have he := hhom z.re hz.1 (z.im / z.re) (hI (Ioo_subset_Icc_self hz.2))
    rw [tangent_decomposition (ne_of_gt hz.1)] at he
    dsimp [F, g]
    rw [he]
    field_simp [ne_of_gt hz.1]
    ring
  have hFzero : F (tangentPoint c) = 0 := by
    rw [hFform _ (tangentPoint_mem hcI)]
    simp
  have hFmax : ∀ z ∈ tangentCone (Ioo a b), F z ≤ F (tangentPoint c) := by
    intro z hz
    rw [hFzero, hFform z hz]
    exact mul_nonpos_of_nonneg_of_nonpos hz.1.le
      (sub_nonpos.mpr (hmax (Ioo_subset_Icc_self hz.2)))
  have heq := eqOn_of_maximum (tangentCone_Ioo_isOpen a b)
    (tangentCone_Ioo_convex a b).isPreconnected hF (tangentPoint_mem hcI) hFmax
  have hgconst : EqOn g (fun _ => g c) (Ioo a b) := by
    intro t ht
    have he := heq (tangentPoint t) (tangentPoint_mem ht)
    rw [hFzero, hFform _ (tangentPoint_mem ht)] at he
    simp only [tangentPoint_re, tangentPoint_im, div_one, one_mul, sub_eq_zero] at he
    exact he
  have hclosed := hgconst.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  have : g a = g c := hclosed (left_mem_Icc.mpr hab.le)
  linarith

/-- Positive homogeneous subharmonic functions are convex in tangent
coordinates. This is the analytic support step, without any root selection
or support inequalities assumed. -/
theorem tangent_convexOn {H : ℂ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hH : SubharmonicOn H (tangentCone S))
    (hhom : ∀ r : ℝ, 0 < r → ∀ t ∈ S,
      H (r • tangentPoint t) = r * H (tangentPoint t)) :
    ConvexOn ℝ S (fun t => H (tangentPoint t)) := by
  apply convexOn_of_slope_mono_adjacent hS
  intro a t b ha hb hat htb
  have hab : a < b := hat.trans htb
  let A : ℝ := (H (tangentPoint b) - H (tangentPoint a)) / (b - a)
  let B : ℝ := H (tangentPoint a) - A * a
  have hea : H (tangentPoint a) = A * a + B := by dsimp [B]; ring
  have heb : H (tangentPoint b) = A * b + B := by
    dsimp [A, B]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hmajor := tangent_chord_majorant hH hhom hab (hS.ordConnected.out ha hb)
    hea.le heb.le t ⟨hat.le, htb.le⟩
  rw [div_le_div_iff₀ (sub_pos.mpr hat) (sub_pos.mpr htb)]
  have hmul := mul_le_mul_of_nonneg_right hmajor (sub_pos.mpr hab).le
  dsimp [A, B] at hmul
  field_simp [ne_of_gt (sub_pos.mpr hab)] at hmul
  nlinarith

def rotation (θ : ℝ) (z : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * z

theorem continuous_rotation (θ : ℝ) : Continuous (rotation θ) := by
  unfold rotation
  fun_prop

theorem norm_rotation_factor (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem rotation_dist (θ : ℝ) (x y : ℂ) : dist (rotation θ x) (rotation θ y) = dist x y := by
  simp only [rotation, dist_eq_norm, ← mul_sub, norm_mul, norm_rotation_factor, one_mul]

theorem rotation_circleMap (θ : ℝ) (c : ℂ) (r t : ℝ) :
    rotation θ (circleMap c r t) = circleMap (rotation θ c) r (t + θ) := by
  simp only [rotation, circleMap, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- Rotation preserves the actual circle submean property. -/
theorem subharmonicOn_rotation {H : ℂ → ℝ} {S : Set ℂ} (hH : SubharmonicOn H S)
    (θ : ℝ) : SubharmonicOn (fun z => H (rotation θ z)) (rotation θ ⁻¹' S) := by
  apply (subharmonicOn_iff_submean
    (hH.cont.comp (continuous_rotation θ).continuousOn (fun _ h => h))).mpr
  intro c r hr hsub
  have hrot : closedBall (rotation θ c) r ⊆ S := by
    intro z hz
    let w := z / Complex.exp ((θ : ℂ) * Complex.I)
    have hw : rotation θ w = z := by
      dsimp [rotation, w]
      field_simp
    have hwm : w ∈ closedBall c r := by
      rw [mem_closedBall, ← rotation_dist θ, hw]
      exact hz
    have h := hsub hwm
    change rotation θ w ∈ S at h
    rwa [hw] at h
  have hmean := (hH.mono hrot).submean hr
  rw [← HarmonicL1Compactness.circleAverage_eq_ray_mean] at hmean ⊢
  have hav : Real.circleAverage (fun z => H (rotation θ z)) c r =
      Real.circleAverage H (rotation θ c) r := by
    rw [Real.circleAverage_eq_integral_add (f := H) θ]
    simp only [Real.circleAverage, rotation_circleMap]
  simpa only [Function.comp_def, hav] using hmean

#print axioms eqOn_of_maximum
#print axioms tangent_convexOn
#print axioms subharmonicOn_rotation
end V10.HomogeneousSubharmonicConvex
