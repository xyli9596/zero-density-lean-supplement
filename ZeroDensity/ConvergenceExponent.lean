import ZeroDensity.CountGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual zero-divisor weights and the finite counting kernel underlying the
convergence-exponent consequence. No claim that the exponential asymptotic
has been obtained from the analytic hypotheses is made here. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeromorphicOn
open scoped Topology BigOperators
namespace ZeroDensity.ConvergenceExponent

/-- Multiplicity-weighted convergence series outside the unit disk. -/
def weight (f : ℂ → ℂ) (q : ℝ) (z : ℂ) : ℝ :=
  if 1 ≤ ‖z‖ then
    ((MeromorphicOn.divisor f univ z).toNat : ℝ) * ‖z‖ ^ (-q)
  else 0

def InfiniteZeroExponent (f : ℂ → ℂ) : Prop :=
  ∀ q : ℝ, 0 < q → ¬ Summable (weight f q)

theorem weight_nonneg (f : ℂ → ℂ) (q : ℝ) (z : ℂ) : 0 ≤ weight f q z := by
  unfold weight
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl

/-- Finite actual divisor mass in a truncated exterior disk is bounded by
r^q times the corresponding finite weighted mass. -/
theorem finite_divisor_bound {f : ℂ → ℂ} {q r : ℝ} (hq : 0 ≤ q)
    (s : Finset ℂ) (hs : ∀ z ∈ s, 1 ≤ ‖z‖ ∧ ‖z‖ ≤ r) :
    (∑ z ∈ s, ((MeromorphicOn.divisor f univ z).toNat : ℝ)) ≤
      r ^ q * ∑ z ∈ s, weight f q z := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  obtain ⟨hz1,hzr⟩ := hs z hz
  have hz0 : 0 < ‖z‖ := zero_lt_one.trans_le hz1
  have hp : 0 < ‖z‖ ^ q := Real.rpow_pos_of_pos hz0 q
  have hm : ‖z‖ ^ q ≤ r ^ q := Real.rpow_le_rpow (norm_nonneg z) hzr hq
  unfold weight
  rw [if_pos hz1, Real.rpow_neg (norm_nonneg z)]
  have hn : 0 ≤ ((MeromorphicOn.divisor f univ z).toNat : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hm hn
  calc
    _ ≤ (r ^ q * ((MeromorphicOn.divisor f univ z).toNat : ℝ)) / ‖z‖ ^ q :=
      (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hh)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Summability gives a single polynomial bound for every finite subset of
actual zeros in the exterior disk. The family of subsets is unrestricted. -/
theorem summable_finite_divisor_bound {f : ℂ → ℂ} {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hw : Summable (weight f q))
    (s : Finset ℂ) (hs : ∀ z ∈ s, 1 ≤ ‖z‖ ∧ ‖z‖ ≤ r) :
    (∑ z ∈ s, ((MeromorphicOn.divisor f univ z).toNat : ℝ)) ≤
      r ^ q * ∑' z, weight f q z := by
  exact (finite_divisor_bound hq s hs).trans
    (mul_le_mul_of_nonneg_left (hw.sum_le_tsum s (fun z _ => weight_nonneg f q z))
      (Real.rpow_nonneg hr q))

/-- The polynomial kernel applies to CountGeometry's actual disk-truncated
count on any angular/pullback domain outside the unit disk. -/
theorem summable_actual_count_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} (hU : ∀ z ∈ U, 1 ≤ ‖z‖) {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hw : Summable (weight f q)) :
    ZeroDensity.CountGeometry.count f U r ≤ r ^ q * ∑' z, weight f q z := by
  classical
  let g : ℂ → ℤ := fun z => if z ∈ U then
    MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z else 0
  have hfinite : (Function.support g).Finite :=
    ZeroDensity.CountGeometry.filtered_support_finite f U r
  let s := hfinite.toFinset
  have ha : AnalyticOnNhd ℂ f univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hs : ∀ z ∈ s, z ∈ U ∧ z ∈ Metric.closedBall (0:ℂ) r := by
    intro z hz
    have hn : g z ≠ 0 := by simpa [s, Function.mem_support] using hz
    have hzU : z ∈ U := by
      by_contra hnU
      exact hn (by simp [g, hnU])
    refine ⟨hzU, ?_⟩
    by_contra hzd
    exact hn (by simp [g, hzU,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzd])
  have he : ZeroDensity.CountGeometry.count f U r =
      ∑ z ∈ s, ((MeromorphicOn.divisor f univ z).toNat : ℝ) := by
    unfold ZeroDensity.CountGeometry.count
    change ((∑ᶠ z, g z : ℤ):ℝ) = _
    rw [finsum_eq_sum_of_support_subset g (show Function.support g ⊆ (s : Set ℂ) from by simp [s]), Int.cast_sum]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hzU,hzd⟩ := hs z hz
    have hd : MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z =
        MeromorphicOn.divisor f univ z := by
      rw [(ha.mono (subset_univ _)).divisor_apply hzd, ha.divisor_apply (mem_univ z)]
    simp only [g, if_pos hzU, hd]
    exact_mod_cast (Int.toNat_of_nonneg (ha.divisor_nonneg z)).symm
  rw [he]
  apply summable_finite_divisor_bound hq hr hw s
  intro z hz
  obtain ⟨hzU,hzd⟩ := hs z hz
  exact ⟨hU z hzU, by simpa [Metric.mem_closedBall, dist_zero_right] using hzd⟩

/-- All inner-disk zeros contribute at most the fixed actual unit-disk
count, uniformly in the counting domain and outer radius. -/
theorem count_le_exterior_add_unit {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (U : Set ℂ) {r : ℝ} (hr : 1 ≤ r) :
    ZeroDensity.CountGeometry.count f U r ≤
      ZeroDensity.CountGeometry.count f (U ∩ {z : ℂ | 1 ≤ ‖z‖}) r +
      ZeroDensity.CountGeometry.count f univ 1 := by
  classical
  let g : ℂ → ℤ := fun z => if z ∈ U then
    MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z else 0
  let o : ℂ → ℤ := fun z => if z ∈ U ∩ {z : ℂ | 1 ≤ ‖z‖} then
    MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z else 0
  let i : ℂ → ℤ := fun z => if z ∈ (univ : Set ℂ) then
    MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) 1) z else 0
  have ha : AnalyticOnNhd ℂ f univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have har : AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) r) := ha.mono (subset_univ _)
  have ha1 : AnalyticOnNhd ℂ f (Metric.closedBall (0:ℂ) 1) := ha.mono (subset_univ _)
  have hg : (Function.support g).Finite :=
    ZeroDensity.CountGeometry.filtered_support_finite f U r
  have ho : (Function.support o).Finite := by
    simpa [o] using ZeroDensity.CountGeometry.filtered_support_finite f (U ∩ {z : ℂ | 1 ≤ ‖z‖}) r
  have hi : (Function.support i).Finite := by
    simpa [i] using ZeroDensity.CountGeometry.filtered_support_finite f univ 1
  have hoi : (Function.support (fun z => o z+i z)).Finite := by
    apply (ho.union hi).subset
    intro z hz
    by_contra hn
    have hn' : o z = 0 ∧ i z = 0 := by
      simpa [Function.mem_support, not_or] using hn
    exact hz (by simp [hn'.1, hn'.2])
  have hle : ∀ z, g z ≤ o z+i z := by
    intro z
    have hin : 0 ≤ i z := by simpa [i] using ha1.divisor_nonneg z
    by_cases hzU : z ∈ U
    · by_cases hzn : 1 ≤ ‖z‖
      · simpa [g,o,hzU,hzn] using le_add_of_nonneg_right (a := MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z) hin
      · have hz1 : z ∈ Metric.closedBall (0:ℂ) 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_lt (lt_of_not_ge hzn))
        have hzr : z ∈ Metric.closedBall (0:ℂ) r := by
          simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_lt (lt_of_not_ge hzn)).trans hr
        have hd : MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) r) z =
            MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) 1) z := by
          rw [har.divisor_apply hzr, ha1.divisor_apply hz1]
        simp [g,o,i,hzU,hzn,hd]
    · have hon : 0 ≤ o z := by
        dsimp [o]; split_ifs
        · exact har.divisor_nonneg z
        · exact le_rfl
      simpa [g,hzU] using add_nonneg hon hin
  have hh := finsum_le_finsum' hg hoi hle
  rw [finsum_add_distrib ho hi] at hh
  unfold ZeroDensity.CountGeometry.count
  exact_mod_cast hh

/-- A convergent divisor series bounds arbitrary-domain counts by a fixed
inner mass plus a polynomial in the outer radius. -/
theorem summable_count_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (U : Set ℂ) {q r : ℝ} (hq : 0 ≤ q) (hr : 1 ≤ r)
    (hw : Summable (weight f q)) :
    ZeroDensity.CountGeometry.count f U r ≤
      ZeroDensity.CountGeometry.count f univ 1 + r ^ q * ∑' z, weight f q z := by
  have hb := summable_actual_count_bound hf
    (U := U ∩ {z : ℂ | 1 ≤ ‖z‖}) (fun z hz => hz.2) hq (zero_le_one.trans hr) hw
  have hc := count_le_exterior_add_unit hf U hr
  linarith

/-- A positive exponential normalized law for actual exterior zero counts
forces every positive-power divisor series to diverge, for any counting domain. -/
theorem infiniteExponent_of_positive_exp_count {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (U : Set ℂ)
    {a β L : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hcount : Tendsto (fun r : ℝ =>
      ZeroDensity.CountGeometry.count f U r / (r ^ β * Real.exp (a*r))) atTop (𝓝 L)) :
    InfiniteZeroExponent f := by
  intro q hq hw
  have hpoly : Tendsto (fun r : ℝ => r ^ (q-β) / Real.exp (a*r)) atTop (𝓝 0) :=
    (isLittleO_rpow_exp_pos_mul_atTop (q-β) ha).tendsto_div_nhds_zero
  have hupper : Tendsto (fun r : ℝ =>
      (r ^ q * ∑' z, weight f q z) / (r ^ β * Real.exp (a*r))) atTop (𝓝 0) := by
    have ht := hpoly.mul_const (∑' z, weight f q z)
    have ht' : Tendsto (fun r : ℝ => (r ^ (q-β) / Real.exp (a*r)) *
        (∑' z, weight f q z)) atTop (𝓝 0) := by simpa using ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [Real.rpow_sub hr]
    ring
  have hinner : Tendsto (fun r : ℝ =>
      ZeroDensity.CountGeometry.count f univ 1 / (r ^ β * Real.exp (a*r)))
      atTop (𝓝 0) := by
    have ht := (isLittleO_rpow_exp_pos_mul_atTop (-β) ha).tendsto_div_nhds_zero
    have ht' := ht.mul_const (ZeroDensity.CountGeometry.count f univ 1)
    apply (show Tendsto (fun r : ℝ => (r ^ (-β) / Real.exp (a*r)) *
      ZeroDensity.CountGeometry.count f univ 1) atTop (𝓝 0) from by simpa using ht').congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [Real.rpow_neg hr.le]
    ring
  have htotal : Tendsto (fun r : ℝ =>
      (ZeroDensity.CountGeometry.count f univ 1 + r ^ q * ∑' z, weight f q z) /
        (r ^ β * Real.exp (a*r))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hinner.add hupper
  have hzero : Tendsto (fun r : ℝ =>
      ZeroDensity.CountGeometry.count f U r / (r ^ β * Real.exp (a*r))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htotal
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
      exact div_nonneg (ZeroDensity.CountGeometry.count_nonneg U r hf)
        (mul_nonneg (Real.rpow_nonneg hr β) (Real.exp_pos _).le)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
      exact div_le_div_of_nonneg_right
        (summable_count_bound hf U hq.le hr hw)
        (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hr) β) (Real.exp_pos _).le)
  have he := tendsto_nhds_unique hcount hzero
  exact (ne_of_gt hL) he

#print axioms count_le_exterior_add_unit
#print axioms summable_count_bound
#print axioms infiniteExponent_of_positive_exp_count
#print axioms summable_actual_count_bound
#print axioms finite_divisor_bound
#print axioms summable_finite_divisor_bound
end ZeroDensity.ConvergenceExponent
