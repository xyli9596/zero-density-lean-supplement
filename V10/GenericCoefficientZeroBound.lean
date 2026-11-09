import V10.CoefficientIntegralZeroBound

/-!
# Actual zero bounds for a general coefficient weight

Only continuity and the local power bound are required of the coefficients.
The solution satisfies the actual monic scalar differential equation. Its
nonzero jet, physical zero multiplicities, and enlarged-set estimate are all
derived here; neither a disk counting bound nor a finite zero measure is an
input to the final theorem.
-/
noncomputable section
open Set Filter Metric MeasureTheory MeromorphicOn
open scoped Topology
namespace V10.GenericCoefficientZeroBound
open BoundedCoefficientZeroCount AffineScalarZeroCount UnitDiskWeightBound
open CoefficientIntegralZeroBound AnalyticZeroMeasureCompact RadialTransfer AtomicCountIntegral
attribute [local instance] Classical.propDecidable

/-- A constant depending only on the order and the local coefficient bound. -/
def boundConstant (n : ℕ) (B : ℝ) : ℝ :=
  diskCountConstant n (1 + (n : ℝ) * B)

theorem boundConstant_pos (n : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 < boundConstant n B := by
  apply diskCountConstant_pos
  positivity

/-- A nonzero entire solution has an everywhere nonzero initial jet, with
no special polynomial-exponential form required of its coefficient row. -/
theorem solution_jet_ne_zero {n : ℕ} (hn : 0 < n) {f : ℂ → ℂ} {b : ℂ → Fin n → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hb : Continuous b)
    (hs : ∀ z, iteratedDeriv n f z + ∑ j : Fin n, b z j * iteratedDeriv j.val f z = 0)
    (hne : ∃ z, f z ≠ 0) (c : ℂ) : ZeroDensity.ScalarLimit.jet n f c ≠ 0 := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨z, hz⟩ := hne
    exact ScalarCompanionODE.jet_nowhere_zero_of_scalar_nontrivial isOpen_univ
      isPreconnected_univ hf hb.continuousOn (fun z _ => hs z)
      ⟨z, mem_univ _, hz⟩ c (mem_univ _)

/-- The actual unit-disk estimate, for any global weight with the stated
local coefficient control. -/
theorem unit_disk_zero_bound {n : ℕ} (hn : 0 < n) {b : ℂ → Fin n → ℂ}
    (hb : Continuous b) {W : ℂ → ℝ} (hW : ∀ z, 1 ≤ W z) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ c w : ℂ, ‖w - c‖ ≤ 5 → ∀ j, ‖b w j‖ ≤ B * W c ^ (n - j.val))
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ z, iteratedDeriv n f z + ∑ j : Fin n, b z j * iteratedDeriv j.val f z = 0)
    (hne : ∃ z, f z ≠ 0) (c : ℂ) :
    unitDiskCount f c ≤ boundConstant n B * W c := by
  have hjet := solution_jet_ne_zero hn hf hb hs hne c
  cases n with
  | zero => omega
  | succ n =>
    unfold unitDiskCount boundConstant
    simp only [Nat.cast_add, Nat.cast_one]
    apply unit_disk_divisor_le hf hs (hW c) hB _ hjet
    intro w hw j
    exact hlocal c w (by simpa only [dist_eq_norm] using mem_closedBall.mp hw) j

/-- Integration of an actual unit-disk bound. This intermediate theorem
separates the finite positive atom argument from the coefficient analysis. -/
theorem bounded_set_zero_bound_of_unit_disk {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {W : ℂ → ℝ} (hW : Continuous W) {C : ℝ}
    (hc : ∀ c, unitDiskCount f c ≤ C * W c)
    {A : Set ℂ} (hA : Bornology.IsBounded A) :
    zeroCount f A ≤ C / Real.pi * ∫ z in cthickening 1 A, W z := by
  let D := cthickening 1 A
  have hD : IsCompact D := isCompact_of_isClosed_isBounded isClosed_cthickening hA.cthickening
  have hlocal : ∀ z ∈ D,
      atomCount (divisorSupport f hD) (fun u => (divisor f D u : ℝ)) (closedBall z 1) ≤
        C * W z := by
    intro z _
    rw [atomCount_divisor_eq_regionCount]
    have hcmp := regionCount_mono_carriers hD (isCompact_closedBall z 1)
      (hf.mono (subset_univ D)) (hf.mono (subset_univ (closedBall z 1)))
      (show closedBall z 1 ∩ D ⊆ univ ∩ closedBall z 1 from fun u hu => ⟨mem_univ u, hu.1⟩)
    have hcount : regionCount f D (closedBall z 1) ≤ unitDiskCount f z := by
      simpa only [regionCount, unitDiskCount, mem_univ, if_true] using hcmp
    exact hcount.trans (hc z)
  have hpos : ∀ u ∈ divisorSupport f hD, 0 ≤ (divisor f D u : ℝ) := by
    intro u _
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.mono (subset_univ D)) u)
  have hi := atomCount_le_integral hpos (hW.continuousOn.integrableOn_compact hD) hlocal
    (E := A)
  rw [atomCount_divisor_eq_regionCount,
    regionCount_eq_zeroCount hf (self_subset_cthickening A)] at hi
  exact hi

/-- The general enlarged-set estimate from the actual equation. -/
theorem bounded_set_zero_bound {n : ℕ} (hn : 0 < n) {b : ℂ → Fin n → ℂ}
    (hb : Continuous b) {W : ℂ → ℝ} (hWc : Continuous W) (hW : ∀ z, 1 ≤ W z)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ c w : ℂ, ‖w - c‖ ≤ 5 → ∀ j, ‖b w j‖ ≤ B * W c ^ (n - j.val))
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ z, iteratedDeriv n f z + ∑ j : Fin n, b z j * iteratedDeriv j.val f z = 0)
    (hne : ∃ z, f z ≠ 0) {A : Set ℂ} (hA : Bornology.IsBounded A) :
    zeroCount f A ≤ boundConstant n B / Real.pi * ∫ z in cthickening 1 A, W z :=
  bounded_set_zero_bound_of_unit_disk hf hWc
    (unit_disk_zero_bound hn hb hW hB hlocal hf hs hne) hA

/-- One solution-independent constant for both conclusions. This is the
interface used by the genuine perturbed equation and its modified weight. -/
theorem exists_uniform_zero_bounds {n : ℕ} (hn : 0 < n) {b : ℂ → Fin n → ℂ}
    (hb : Continuous b) {W : ℂ → ℝ} (hWc : Continuous W) (hW : ∀ z, 1 ≤ W z)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ c w : ℂ, ‖w - c‖ ≤ 5 → ∀ j, ‖b w j‖ ≤ B * W c ^ (n - j.val)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ z, iteratedDeriv n f z + ∑ j : Fin n, b z j * iteratedDeriv j.val f z = 0) →
      (∃ z, f z ≠ 0) →
      (∀ c : ℂ, zeroCount f (closedBall c 1) ≤ C * W c) ∧
      (∀ A : Set ℂ, Bornology.IsBounded A →
        zeroCount f A ≤ C * ∫ z in cthickening 1 A, W z) := by
  let C := boundConstant n B * (1 + 1 / Real.pi)
  have hC : 0 < C := mul_pos (boundConstant_pos n hB) (by positivity)
  have hbase : boundConstant n B ≤ C := by
    dsimp [C]
    nlinarith [boundConstant_pos n hB,
      div_nonneg (by norm_num : (0 : ℝ) ≤ 1) Real.pi_pos.le]
  have hint : boundConstant n B / Real.pi ≤ C := by
    dsimp [C]
    rw [mul_add, mul_one, mul_one_div]
    linarith [boundConstant_pos n hB]
  refine ⟨C, hC, ?_⟩
  intro f hf hs hne
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
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
    exact (unit_disk_zero_bound hn hb hW hB hlocal ha hs hne c).trans
      (mul_le_mul_of_nonneg_right hbase (le_trans zero_le_one (hW c)))
  · intro A hA
    exact (bounded_set_zero_bound hn hb hWc hW hB hlocal ha hs hne hA).trans
      (mul_le_mul_of_nonneg_right hint (integral_nonneg fun z => le_trans zero_le_one (hW z)))

#print axioms unit_disk_zero_bound
#print axioms bounded_set_zero_bound
#print axioms exists_uniform_zero_bounds
end V10.GenericCoefficientZeroBound
