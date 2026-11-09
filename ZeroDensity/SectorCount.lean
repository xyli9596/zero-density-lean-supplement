import CRGZeroDistributionSector
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Conditional annular-to-radial counting step. The distributional Laplacian
identity and L¹-to-annular convergence are not yet formalized. -/
noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace ZeroDensity.SectorCount

theorem dyadic_error_bound {E : ℝ → ℝ} {T δ B : ℝ}
    (hT : 0 < T) (_hδ : 0 ≤ δ)
    (hbase : ∀ t ∈ Icc T (2*T), |E t| ≤ B)
    (hstep : ∀ t ≥ T, |E (2*t)-E t| ≤ δ*t) :
    ∀ k : ℕ, ∀ t ∈ Icc T (2*T),
      |E ((2:ℝ)^k*t)| ≤ B+δ*(((2:ℝ)^k-1)*t) := by
  intro k
  induction k with
  | zero => intro t ht; simpa using hbase t ht
  | succ k ih =>
    intro t ht
    have ht0 : 0 ≤ t := (hT.trans_le ht.1).le
    have hscale : T ≤ (2:ℝ)^k*t := ht.1.trans (by
      simpa using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) ht0)
    have heq : (2:ℝ)^(k+1)*t = 2*((2:ℝ)^k*t) := by rw [pow_succ]; ring
    calc
      |E ((2:ℝ)^(k+1)*t)| ≤ |E (2*((2:ℝ)^k*t))-E ((2:ℝ)^k*t)| + |E ((2:ℝ)^k*t)| := by
        rw [heq]; simpa using abs_add_le (E (2*((2:ℝ)^k*t))-E ((2:ℝ)^k*t)) (E ((2:ℝ)^k*t))
      _ ≤ δ*((2:ℝ)^k*t)+(B+δ*(((2:ℝ)^k-1)*t)) := add_le_add (hstep _ hscale) (ih t ht)
      _ = _ := by rw [pow_succ]; ring

/-- Signed errors and a bounded inner remainder suffice, also when c ≠ 0. -/
theorem radial_of_annular {N : ℝ → ℝ} {c : ℝ}
    (hbounded : ∀ T > 0, ∃ B : ℝ, ∀ t ∈ Icc T (2*T), |N t-c*t| ≤ B)
    (hann : Tendsto (fun t : ℝ => (N (2*t)-N t)/t) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => N t/t) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := Metric.tendsto_atTop.mp hann (ε/2) (by linarith)
  let T := max 1 a
  have hT : 0 < T := zero_lt_one.trans_le (le_max_left ..)
  obtain ⟨B,hB⟩ := hbounded T hT
  have hstep : ∀ t ≥ T, |(N (2*t)-c*(2*t))-(N t-c*t)| ≤ (ε/2)*t := by
    intro t ht
    have ht0 : 0 < t := hT.trans_le ht
    have hh := ha t ((le_max_right 1 a).trans ht)
    rw [Real.dist_eq] at hh
    have he : (N (2*t)-c*(2*t))-(N t-c*t) = ((N (2*t)-N t)/t-c)*t := by field_simp; ring
    rw [he, abs_mul, abs_of_pos ht0]
    exact (mul_lt_mul_of_pos_right hh ht0).le
  have hlim : Tendsto (fun t : ℝ => B/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨b,hb⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2)))
  refine ⟨max T b, ?_⟩
  intro r hr
  have hTr : T ≤ r := (le_max_left ..).trans hr
  have hr0 : 0 < r := hT.trans_le hTr
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hT).mpr (by simpa using hTr)) (by norm_num : (1:ℝ)<2)
  let t := r/(2:ℝ)^k
  have hp : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
  have ht : t ∈ Icc T (2*T) := by
    constructor
    · apply (le_div_iff₀ hp).mpr
      have := (le_div_iff₀ hT).mp hlo
      nlinarith
    · apply (div_le_iff₀ hp).mpr
      have := (div_lt_iff₀ hT).mp hhi
      rw [pow_succ] at this
      nlinarith
  have heq : (2:ℝ)^k*t = r := by dsimp [t]; field_simp
  have hh := dyadic_error_bound hT (by linarith : 0 ≤ ε/2) hB hstep k t ht
  rw [heq] at hh
  have herr : |N r-c*r| ≤ B+(ε/2)*r := by
    have ht0 : 0 ≤ t := (hT.trans_le ht.1).le
    have hm : ((2:ℝ)^k-1)*t ≤ r := by rw [←heq]; nlinarith
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hm (show 0 ≤ ε/2 by linarith)) B)
  rw [Real.dist_eq]
  have hid : N r/r-c = (N r-c*r)/r := by field_simp
  rw [hid, abs_div, abs_of_pos hr0]
  apply (div_lt_iff₀ hr0).mpr
  have hb' := (div_lt_iff₀ hr0).mp (hb r ((le_max_right ..).trans hr))
  linarith

open CRGZeroDistributionSector CRGZeroDistributionScaled LevinGrowth

/-- Actual compact-sector divisor counts, conditional only on their annular
asymptotic. This specialization uses entire functions and compact direction
sets; exterior analytic domains and open angular boundaries remain pending. -/
theorem actual_sector_count_of_annular {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {D : Set Direction} (hD : IsCompact D) {c : ℝ}
    (hann : Tendsto (fun t : ℝ =>
      (zeroCount f (radialSector D (2*t)) - zeroCount f (radialSector D t))/t)
      atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => zeroCount f (radialSector D t)/t) atTop (𝓝 c) := by
  apply radial_of_annular _ hann
  intro T hT
  refine ⟨zeroCount f (radialSector D (2*T)) + |c| *(2*T), ?_⟩
  intro t ht
  have hn := zeroCount_radialSector_nonneg hf D t
  have hu := zeroCount_radialSector_monotone hf hD ht.2
  have ht0 : 0 ≤ t := (hT.trans_le ht.1).le
  calc
    |zeroCount f (radialSector D t)-c*t| ≤
        |zeroCount f (radialSector D t)| + |c*t| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (zeroCount f (radialSector D t)) (-(c*t))
    _ = zeroCount f (radialSector D t)+|c| *t := by rw [abs_of_nonneg hn, abs_mul, abs_of_nonneg ht0]
    _ ≤ _ := add_le_add hu (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg c))

/-- A fixed change of inner cutoff has zero effect on normalized density. -/
theorem count_shift {N : ℝ → ℝ} {c b : ℝ}
    (h : Tendsto (fun r : ℝ => N r/r) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ => (N r-b)/r) atTop (𝓝 c) := by
  have hb : Tendsto (fun r : ℝ => b/r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa only [sub_div, sub_zero] using h.sub hb

#print axioms dyadic_error_bound
#print axioms radial_of_annular
#print axioms actual_sector_count_of_annular
#print axioms count_shift
end ZeroDensity.SectorCount
