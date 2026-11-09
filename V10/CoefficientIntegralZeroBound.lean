import V10.UnitDiskWeightBound
import V10.AtomicCountIntegral

/-!
# Lemma 4.1: actual unit-disk and enlarged-set zero bounds

The constant is constructed solely from the equation's finite polynomial and
frequency data. The count uses the actual analytic divisor of the original
entire solution. A compact carrier is introduced only inside the proof to
justify finite positive atom integration, then removed from the conclusion.
-/
noncomputable section
open Set Filter Metric MeasureTheory MeromorphicOn
open scoped Topology
namespace V10.CoefficientIntegralZeroBound
open ZeroDensity.Statement CoefficientWeight UnitDiskWeightBound
open AnalyticZeroMeasureCompact RadialTransfer AtomicCountIntegral
attribute [local instance] Classical.propDecidable

/-- Actual zero multiplicities filtered by a physical set. For bounded sets
and a nonzero entire solution the proof below supplies finite support. -/
def zeroCount (f : ℂ → ℂ) (E : Set ℂ) : ℝ := regionCount f univ E

theorem atomCount_divisor_eq_regionCount (f : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (A : Set ℂ) :
    atomCount (divisorSupport f hK) (fun z => (divisor f K z : ℝ)) A = regionCount f K A := by
  classical
  unfold atomCount regionCount
  have hs : Function.support (fun z => if z ∈ A then divisor f K z else (0 : ℤ)) ⊆
      (divisorSupport f hK : Set ℂ) := by
    intro z hz
    apply (mem_divisorSupport hK).mpr
    by_contra hn
    apply hz
    simp [hn]
  rw [finsum_eq_sum_of_support_subset _ hs, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs <;> simp

/-- On counted points inside a carrier, the actual divisor is independent
of whether it was defined on that carrier or on the entire plane. -/
theorem regionCount_eq_zeroCount {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {K A : Set ℂ} (hAK : A ⊆ K) : regionCount f K A = zeroCount f A := by
  rw [zeroCount, regionCount_eq_mem_sum, regionCount_eq_mem_sum]
  congr 1
  apply finsum_mem_congr rfl
  intro z hz
  exact ZeroDensity.SectorDivisorCount.divisor_domains_eq (hf.mono (subset_univ K)) hf
    (hAK hz) (mem_univ z)

/-- The enlarged-set integral bound, with its explicit factor 1/π. The set
may have open angular or radial boundaries; only boundedness is needed. -/
theorem bounded_set_zero_bound {n : ℕ} (E : EquationData n) {f : ℂ → ℂ}
    (hf : IsSolution E f) (hn : ∃ z, f z ≠ 0) {A : Set ℂ} (hA : Bornology.IsBounded A) :
    zeroCount f A ≤ boundConstant E / Real.pi * ∫ z in cthickening 1 A, weight E z := by
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1
  let D := cthickening 1 A
  have hD : IsCompact D := isCompact_of_isClosed_isBounded isClosed_cthickening hA.cthickening
  have hlocal : ∀ z ∈ D,
      atomCount (divisorSupport f hD) (fun u => (divisor f D u : ℝ)) (closedBall z 1) ≤
        boundConstant E * weight E z := by
    intro z hz
    rw [atomCount_divisor_eq_regionCount]
    have hc : regionCount f D (closedBall z 1) ≤ unitDiskCount f z := by
      have hcmp := regionCount_mono_carriers hD (isCompact_closedBall z 1)
        (ha.mono (subset_univ D)) (ha.mono (subset_univ (closedBall z 1)))
        (show closedBall z 1 ∩ D ⊆ univ ∩ closedBall z 1 from fun u hu => ⟨mem_univ u, hu.1⟩)
      simpa only [regionCount, unitDiskCount, mem_univ, if_true] using hcmp
    exact hc.trans (unit_disk_zero_bound E hf hn z)
  have hb := atomCount_le_integral
    (Z := divisorSupport f hD) (w := fun u => (divisor f D u : ℝ)) (E := A)
    (fun u _ => by
      exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (ha.mono (subset_univ D)) u))
    ((weight_continuous E).continuousOn.integrableOn_compact hD) hlocal
  rw [atomCount_divisor_eq_regionCount,
    regionCount_eq_zeroCount ha (self_subset_cthickening A)] at hb
  exact hb

/-- Both conclusions of current Lemma 4.1 hold with the same positive
constant, depending only on n and the original equation coefficients. -/
theorem lemma_4_1 {n : ℕ} (E : EquationData n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, IsSolution E f → (∃ z, f z ≠ 0) →
      (∀ c : ℂ, zeroCount f (closedBall c 1) ≤ C * weight E c) ∧
      (∀ A : Set ℂ, Bornology.IsBounded A → MeasurableSet A →
        zeroCount f A ≤ C * ∫ z in cthickening 1 A, weight E z) := by
  let C := boundConstant E * (1 + 1 / Real.pi)
  have hC : 0 < C := mul_pos (boundConstant_pos E) (by positivity)
  have hbase : boundConstant E ≤ C := by
    dsimp [C]
    nlinarith [boundConstant_pos E, Real.pi_pos, div_nonneg (by norm_num : (0 : ℝ) ≤ 1) Real.pi_pos.le]
  have hint : boundConstant E / Real.pi ≤ C := by
    dsimp [C]
    rw [mul_add, mul_one, mul_one_div]
    linarith [boundConstant_pos E]
  refine ⟨C, hC, ?_⟩
  intro f hf hn
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1
  constructor
  · intro c
    have he : zeroCount f (closedBall c 1) = unitDiskCount f c := by
      rw [← regionCount_eq_zeroCount ha (subset_refl (closedBall c 1))]
      unfold regionCount unitDiskCount
      congr 1
      apply finsum_congr
      intro z
      by_cases hz : z ∈ closedBall c 1 <;> simp [hz]
    rw [he]
    exact (unit_disk_zero_bound E hf hn c).trans
      (mul_le_mul_of_nonneg_right hbase (zero_lt_one.trans_le (weight_ge_one E c)).le)
  · intro A hA _
    exact (bounded_set_zero_bound E hf hn hA).trans
      (mul_le_mul_of_nonneg_right hint (integral_nonneg fun z =>
        (zero_lt_one.trans_le (weight_ge_one E z)).le))

#print axioms bounded_set_zero_bound
#print axioms lemma_4_1
end V10.CoefficientIntegralZeroBound
