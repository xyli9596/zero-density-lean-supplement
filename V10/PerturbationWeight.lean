import V10.PerturbationGrowth
import V10.CoefficientWeight
import V10.ExponentialScales
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual added coefficients and actual added area mass in Theorem 1.5.
The mass estimate below uses a disk supremum bound; this suffices for the
required little-o conclusion without assuming a tail estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology
namespace V10.PerturbationWeight
open ZeroDensity.Statement ZeroDensity.CoefficientData CoefficientWeight
open ExponentialScales

def weight {n : ℕ} (E : EquationData n) (b : ℝ) (z : ℂ) : ℝ :=
  CoefficientWeight.weight E z + Real.exp (b * ‖z‖)

theorem weight_ge_one {n : ℕ} (E : EquationData n) (b : ℝ) (z : ℂ) :
    1 ≤ weight E b z := by
  have h := CoefficientWeight.weight_ge_one E z
  dsimp [weight]
  linarith [Real.exp_pos (b * ‖z‖)]

theorem weight_continuous {n : ℕ} (E : EquationData n) (b : ℝ) :
    Continuous (weight E b) :=
  (CoefficientWeight.weight_continuous E).add (by fun_prop)

/-- The actual coefficient A_j+R_j obeys a uniform power-weight estimate on
every physical radius-five neighborhood. -/
theorem coefficient_local_bound {n : ℕ} (E : EquationData n)
    {R : Fin n → ℂ → ℂ} {b C : ℝ} (hb : 0 < b) (hC : 0 < C)
    (hR : ∀ j z, ‖R j z‖ ≤ C * Real.exp ((gap j : ℝ) * b * ‖z‖))
    (j : Fin n) {z w : ℂ} (hw : ‖w - z‖ ≤ 5) :
    ‖E.coefficient j w + R j w‖ ≤
      (localConstant E + C * Real.exp (5 * n * b)) * weight E b z ^ gap j := by
  have hn : ‖w‖ ≤ ‖z‖ + 5 := by
    have hh := norm_add_le (w - z) z
    rw [sub_add_cancel] at hh
    linarith
  have hg : 0 ≤ (gap j : ℝ) := Nat.cast_nonneg _
  have hgn : (gap j : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le n j.val)
  have he : (gap j : ℝ) * b * ‖w‖ ≤ (gap j : ℝ) * (b * ‖z‖) + 5 * n * b := by
    nlinarith [mul_nonneg hg hb.le, mul_le_mul_of_nonneg_left hn (mul_nonneg hg hb.le),
      mul_le_mul_of_nonneg_right hgn hb.le]
  have hR' : ‖R j w‖ ≤ (C * Real.exp (5 * n * b)) *
      (Real.exp (b * ‖z‖)) ^ gap j := by
    calc
      _ ≤ C * Real.exp ((gap j : ℝ) * b * ‖w‖) := hR j w
      _ ≤ C * Real.exp ((gap j : ℝ) * (b * ‖z‖) + 5 * n * b) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC.le
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]; ring
  have hW : 0 ≤ CoefficientWeight.weight E z :=
    le_trans zero_le_one (CoefficientWeight.weight_ge_one E z)
  have hw₁ : CoefficientWeight.weight E z ≤ weight E b z :=
    le_add_of_nonneg_right (Real.exp_nonneg _)
  have hw₂ : Real.exp (b * ‖z‖) ≤ weight E b z := le_add_of_nonneg_left hW
  calc
    _ ≤ ‖E.coefficient j w‖ + ‖R j w‖ := norm_add_le _ _
    _ ≤ localConstant E * CoefficientWeight.weight E z ^ gap j +
        (C * Real.exp (5 * n * b)) * (Real.exp (b * ‖z‖)) ^ gap j :=
      add_le_add (CoefficientWeight.coefficient_local_bound E j hw) hR'
    _ ≤ localConstant E * weight E b z ^ gap j +
        (C * Real.exp (5 * n * b)) * weight E b z ^ gap j :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW hw₁ _) (localConstant_pos E).le)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) hw₂ _)
          (mul_nonneg hC.le (Real.exp_nonneg _)))
    _ = _ := by ring

/-- A global bound for the actual integral of the added exponential weight. -/
theorem disk_mass_bound {b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) :
    (∫ z : ℂ in closedBall 0 T, Real.exp (b * ‖z‖)) ≤
      Real.pi * T ^ 2 * Real.exp (b * T) := by
  have hi : IntegrableOn (fun z : ℂ => Real.exp (b * ‖z‖)) (closedBall 0 T) :=
    (by fun_prop : Continuous (fun z : ℂ => Real.exp (b * ‖z‖))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 T)
  calc
    _ ≤ ∫ _z : ℂ in closedBall 0 T, Real.exp (b * T) :=
      setIntegral_mono_on hi (integrableOn_const (isCompact_closedBall (0 : ℂ) T).measure_ne_top)
        measurableSet_closedBall (fun z hz => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (by simpa using hz : ‖z‖ ≤ T) hb))
    _ = _ := by
      rw [integral_const]
      simp [Measure.real, Complex.volume_closedBall, hT, mul_comm]

/-- On every fixed enlargement, the actual added mass is negligible on every
leading scale with a strict exponential gap, including the paper's D(r). -/
theorem disk_mass_littleO {a b d : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hba : b < a) (hd : 0 ≤ d) (β : ℝ) :
    (fun r : ℝ => ∫ z : ℂ in closedBall 0 (r + d), Real.exp (b * ‖z‖))
      =o[atTop] globalScale a β := by
  have hsmall : (fun r : ℝ => ∫ z : ℂ in closedBall 0 (r + d), Real.exp (b * ‖z‖))
      =o[atTop] scale a (β + 1 / 2) := by
    apply negligible_of_exp_bound (C := Real.pi * (1 + d) ^ 2 * Real.exp (b * d))
      (N := 2) hba
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := by linarith
    have hrd : 0 ≤ r + d := add_nonneg hr0 hd
    have hle : r + d ≤ (1 + d) * r := by nlinarith
    have hsq : (r + d) ^ 2 ≤ (1 + d) ^ 2 * r ^ 2 := by nlinarith
    rw [abs_of_nonneg (integral_nonneg fun _ => Real.exp_nonneg _)]
    calc
      _ ≤ Real.pi * (r + d) ^ 2 * Real.exp (b * (r + d)) := disk_mass_bound hb hrd
      _ ≤ Real.pi * ((1 + d) ^ 2 * r ^ 2) * Real.exp (b * (r + d)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le)
          (Real.exp_nonneg _)
      _ = _ := by
        simp only [scale, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
        rw [mul_add, Real.exp_add]
        ring
  have hc : a ^ (β + 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  have hmul := hsmall.const_mul_right hc
  apply hmul.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (globalScale_eq ha hr β).symm

#print axioms coefficient_local_bound
#print axioms disk_mass_littleO
end V10.PerturbationWeight
