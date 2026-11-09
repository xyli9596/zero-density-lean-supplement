import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# The concrete sampling radii in v10 Theorem 1.4

The sample is `sqrt (m + 1)` for `m : ℕ`. Its radii grow strictly to
infinity, its gaps vanish, and the reciprocal phase normalization is
summable for `a > 0`, `β ≥ 0`. Summability is derived from the fourth
term of the exponential series and the convergent p-series of exponent 2;
it is not an input hypothesis.
-/

noncomputable section
open Filter
open scoped Topology NNReal ENNReal

namespace V10.SamplingScale

def radius (m : ℕ) : ℝ := Real.sqrt ((m : ℝ) + 1)

def phaseScale (a β : ℝ) (m : ℕ) : ℝ :=
  (a * radius m) ^ β * Real.exp (a * radius m)

def globalScale (a β : ℝ) (m : ℕ) : ℝ :=
  phaseScale a (β + 1 / 2) m

lemma radius_pos (m : ℕ) : 0 < radius m := by
  unfold radius
  positivity

lemma radius_sq (m : ℕ) : radius m ^ 2 = (m : ℝ) + 1 := by
  exact Real.sq_sqrt (by positivity)

lemma one_le_radius (m : ℕ) : 1 ≤ radius m := by
  have hp := radius_pos m
  have hs := radius_sq m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem radius_strictMono : StrictMono radius := by
  intro m n hmn
  apply Real.sqrt_lt_sqrt (by positivity)
  exact_mod_cast Nat.succ_lt_succ hmn

theorem radius_tendsto : Tendsto radius atTop atTop := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  exact Real.tendsto_sqrt_atTop.comp hnat

/-- Rationalization gives the exact gap, including all small indices. -/
lemma radius_gap_eq (m : ℕ) :
    radius (m + 1) - radius m = 1 / (radius (m + 1) + radius m) := by
  have hden : radius (m + 1) + radius m ≠ 0 :=
    (add_pos (radius_pos (m + 1)) (radius_pos m)).ne'
  apply (eq_div_iff hden).mpr
  have h0 := radius_sq m
  have h1 := radius_sq (m + 1)
  push_cast at h1
  nlinarith

theorem radius_gap_tendsto_zero :
    Tendsto (fun m => radius (m + 1) - radius m) atTop (𝓝 0) := by
  have hinv : Tendsto (fun m => 1 / radius m) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop radius_tendsto
  apply squeeze_zero (fun m => (radius_strictMono (Nat.lt_succ_self m)).le |> sub_nonneg.mpr)
    (fun m => ?_) hinv
  rw [radius_gap_eq]
  apply one_div_le_one_div_of_le (radius_pos m)
  linarith [radius_pos (m + 1)]

lemma phaseScale_pos {a : ℝ} (ha : 0 < a) (β : ℝ) (m : ℕ) :
    0 < phaseScale a β m := by
  unfold phaseScale
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos ha (radius_pos m)) β) (Real.exp_pos _)

/-- A completely explicit p-series majorant, valid at every index. -/
theorem reciprocal_phaseScale_le {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) (m : ℕ) :
    (phaseScale a β m)⁻¹ ≤ (24 / (a ^ β * a ^ 4)) * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hmul : a ≤ a * radius m := by nlinarith [one_le_radius m]
  have hpre : a ^ β ≤ (a * radius m) ^ β :=
    Real.rpow_le_rpow ha.le hmul hβ
  have hpow : (a * radius m) ^ 4 = a ^ 4 * ((m : ℝ) + 1) ^ 2 := by
    calc
      (a * radius m) ^ 4 = a ^ 4 * (radius m ^ 2) ^ 2 := by ring
      _ = _ := by rw [radius_sq]
  have hexp : a ^ 4 * ((m : ℝ) + 1) ^ 2 / 24 ≤ Real.exp (a * radius m) := by
    have h := Real.pow_div_factorial_le_exp (a * radius m)
      (mul_nonneg ha.le (radius_pos m).le) 4
    norm_num [Nat.factorial] at h
    rwa [hpow] at h
  have hlow : a ^ β * (a ^ 4 * ((m : ℝ) + 1) ^ 2 / 24) ≤ phaseScale a β m := by
    unfold phaseScale
    exact mul_le_mul hpre hexp (by positivity)
      (Real.rpow_nonneg (mul_nonneg ha.le (radius_pos m).le) β)
  have hp : 0 < a ^ β * (a ^ 4 * ((m : ℝ) + 1) ^ 2 / 24) := by positivity
  calc
    (phaseScale a β m)⁻¹ = 1 / phaseScale a β m := by rw [one_div]
    _ ≤ 1 / (a ^ β * (a ^ 4 * ((m : ℝ) + 1) ^ 2 / 24)) :=
      one_div_le_one_div_of_le hp hlow
    _ = _ := by
      field_simp [ha.ne', (Real.rpow_pos_of_pos ha β).ne',
        (show (0 : ℝ) < (m : ℝ) + 1 by positivity).ne']

/-- The summability hypothesis needed by the projection-series lemma is
proved for the actual sample and scale. -/
theorem summable_reciprocal_phaseScale {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    Summable (fun m : ℕ => (phaseScale a β m)⁻¹) := by
  have hp : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    simpa only [Real.rpow_two, sq_abs] using
      (Real.summable_one_div_nat_add_rpow (1 : ℝ) (2 : ℝ)).mpr (by norm_num)
  exact Summable.of_nonneg_of_le
    (fun m => (inv_pos.mpr (phaseScale_pos ha β m)).le)
    (reciprocal_phaseScale_le ha hβ) (hp.mul_left (24 / (a ^ β * a ^ 4)))

/-- Neighboring radii have relative ratio tending to one. -/
theorem radius_ratio_tendsto_one :
    Tendsto (fun m => radius (m + 1) / radius m) atTop (𝓝 1) := by
  have hzero : Tendsto (fun m => (radius (m + 1) - radius m) / radius m)
      atTop (𝓝 (0 : ℝ)) := radius_gap_tendsto_zero.div_atTop radius_tendsto
  have h := hzero.add_const 1
  simp only [zero_add] at h
  apply h.congr
  intro m
  field_simp [(radius_pos m).ne']
  ring

/-- Ratio stability holds for every real polynomial exponent. -/
theorem phaseScale_ratio_tendsto_one {a : ℝ} (ha : 0 < a) (β : ℝ) :
    Tendsto (fun m => phaseScale a β (m + 1) / phaseScale a β m) atTop (𝓝 1) := by
  have hp : Tendsto (fun m => (radius (m + 1) / radius m) ^ β) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using
      radius_ratio_tendsto_one.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have he : Tendsto (fun m => Real.exp (a * (radius (m + 1) - radius m)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp (radius_gap_tendsto_zero.const_mul a)
  have ht := hp.mul he
  simp only [one_mul] at ht
  apply ht.congr
  intro m
  unfold phaseScale
  rw [mul_sub, Real.exp_sub]
  have hdiv : (a * radius (m + 1)) / (a * radius m) = radius (m + 1) / radius m := by
    field_simp [ha.ne']
  rw [← hdiv, Real.div_rpow (mul_nonneg ha.le (radius_pos (m + 1)).le)
    (mul_nonneg ha.le (radius_pos m).le)]
  ring

/-- The exact global mass normalization has adjacent sample ratio one. -/
theorem globalScale_ratio_tendsto_one {a : ℝ} (ha : 0 < a) (β : ℝ) :
    Tendsto (fun m => globalScale a β (m + 1) / globalScale a β m) atTop (𝓝 1) :=
  phaseScale_ratio_tendsto_one ha (β + 1 / 2)

/-- Positive NNReal realization, ready for `ProjectionSeries`. -/
def phaseScaleNNReal (a β : ℝ) (m : ℕ) : ℝ≥0 :=
  Real.toNNReal (phaseScale a β m)

lemma phaseScaleNNReal_pos {a : ℝ} (ha : 0 < a) (β : ℝ) (m : ℕ) :
    0 < phaseScaleNNReal a β m :=
  Real.toNNReal_pos.mpr (phaseScale_pos ha β m)

lemma coe_phaseScaleNNReal {a : ℝ} (ha : 0 < a) (β : ℝ) (m : ℕ) :
    (phaseScaleNNReal a β m : ℝ) = phaseScale a β m :=
  Real.coe_toNNReal _ (phaseScale_pos ha β m).le

/-- No summability assumption is needed to instantiate the NNReal
normalization interface in `ProjectionSeries`. -/
theorem summable_reciprocal_phaseScaleNNReal {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    Summable (fun m : ℕ => (phaseScaleNNReal a β m)⁻¹) := by
  apply NNReal.summable_coe.mp
  simpa only [NNReal.coe_inv, coe_phaseScaleNNReal ha] using
    summable_reciprocal_phaseScale ha hβ

theorem tsum_reciprocal_phaseScaleNNReal_ne_top {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    (∑' m : ℕ, (phaseScaleNNReal a β m : ℝ≥0∞)⁻¹) ≠ ∞ := by
  simp_rw [← ENNReal.coe_inv (phaseScaleNNReal_pos ha β _).ne']
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
    (summable_reciprocal_phaseScaleNNReal ha hβ)

#print axioms radius_gap_tendsto_zero
#print axioms summable_reciprocal_phaseScale
#print axioms globalScale_ratio_tendsto_one
#print axioms tsum_reciprocal_phaseScaleNNReal_ne_top

end V10.SamplingScale
