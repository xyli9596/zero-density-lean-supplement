import V10.ScalarCompactnessMovingCenter
import V10.ScalarCompanionODE
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A linear zero-count bound from bounded actual ODE coefficients

Straight-segment Gronwall controls the normalized jet on a large disk. Cauchy's
estimate supplies a nonzero scalar sample, and genuine moving-center Jensen
bounds the actual divisor. The constant is independent of the solution and
of the radius. This proves the analytic disk-count input of Lemma 4.1 without
assuming an argument-variation or zero-count estimate.
-/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace V10.BoundedCoefficientZeroCount
open ZeroDensity.ScalarLimit ScalarCompactnessMovingCenter

/-- Straight-line Gronwall on a convex complex domain, without nonvanishing
or differentiability of the vector norm as hypotheses. -/
theorem convex_solution_norm_upper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : Convex ℝ D) {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {M : ℝ}
    (hode : ∀ z ∈ D, HasDerivAt Y (A z (Y z)) z)
    (hA : ∀ z ∈ D, ‖A z‖ ≤ M) {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) :
    ‖Y w‖ ≤ ‖Y z‖ * Real.exp (M * ‖w - z‖) := by
  let path : ℝ → ℂ := fun t => z + (t : ℂ) * (w - z)
  let C : ℝ → E →L[ℝ] E := fun t =>
    (((w - z) • A (path t)) : E →L[ℂ] E).restrictScalars ℝ
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D := by
    intro t ht
    simpa [path, Complex.real_smul] using hD.add_smul_sub_mem hz hw ht
  have hpder (t : ℝ) : HasDerivAt path (w - z) t := by
    simpa only [path, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - z)).const_add z
  have ho : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => Y (path t))
      (C t (Y (path t))) t := by
    intro t ht
    change HasDerivAt (fun t => Y (path t)) ((w - z) • (A (path t)) (Y (path t))) t
    exact (hode _ (hpath t ht)).scomp t (hpder t)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t‖ ≤ M * ‖w - z‖ := by
    intro t ht
    simp only [C, ContinuousLinearMap.norm_restrictScalars, norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hA _ (hpath t ht)) (norm_nonneg (w - z))
  simpa [path] using ZeroDensity.PerronEstimates.solution_norm_upper
    (show (0 : ℝ) ≤ 1 by norm_num) ho hC

theorem jet_const_mul (n : ℕ) (k : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    jet n (fun w => k * f w) z = k • jet n f z := by
  ext j
  exact iteratedDeriv_const_mul_field k f

/-- Multiplying by a nonzero constant preserves the actual divisor, including
its totalized value at any identically zero germ. -/
theorem divisor_const_mul {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    {k : ℂ} (hk : k ≠ 0) (z : ℂ) :
    MeromorphicOn.divisor (fun w => k * f w) K z = MeromorphicOn.divisor f K z := by
  by_cases hz : z ∈ K
  · change MeromorphicOn.divisor ((fun _ => k) * f) K z = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
        (fun w hw => analyticAt_const.mul (hf w hw)) hz,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
    congr 1
    rw [analyticOrderAt_mul analyticAt_const (hf z hz),
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => k) z).analyticOrderAt_eq_zero.mpr hk, zero_add]
  · simp [hz]

def diskCountConstant (n : ℕ) (M : ℝ) : ℝ :=
  (5 * M + Real.log (cauchyConstant n 1) + 1) / Real.log (4 / 3 : ℝ)

theorem cauchyConstant_one_ge_one (n : ℕ) : 1 ≤ cauchyConstant n 1 := by
  unfold cauchyConstant
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

theorem diskCountConstant_pos (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < diskCountConstant n M := by
  have hlog := Real.log_nonneg (cauchyConstant_one_ge_one n)
  unfold diskCountConstant
  exact div_pos (by positivity) (Real.log_pos (by norm_num))

/-- Actual bounded jet ODE on the fivefold disk gives a linear count on the
inner disk. Its only nontriviality premise is the actual initial jet ≠ 0. -/
theorem disk_divisor_le_of_jet_ode {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {R M : ℝ} (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hv : AnalyticOnNhd ℂ v (closedBall 0 (5 * R)))
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hode : ∀ z ∈ closedBall 0 (5 * R), HasDerivAt (jet n v) (A z (jet n v z)) z)
    (hA : ∀ z ∈ closedBall 0 (5 * R), ‖A z‖ ≤ M)
    (hne : jet n v 0 ≠ 0) :
    ((∑ᶠ z, MeromorphicOn.divisor v (closedBall 0 R) z : ℤ) : ℝ) ≤
      diskCountConstant n M * R := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  let J := ‖jet n v 0‖
  have hJ : 0 < J := norm_pos_iff.mpr hne
  let k : ℂ := (J : ℂ)⁻¹
  have hk : k ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hJ.ne')
  let f : ℂ → ℂ := fun z => k * v z
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (5 * R)) :=
    fun z hz => analyticAt_const.mul (hv z hz)
  have hkNorm : ‖k‖ = J⁻¹ := by simp [k, abs_of_pos hJ]
  have hfjet : ‖jet n f 0‖ = 1 := by
    rw [show f = (fun z => k * v z) from rfl, jet_const_mul, norm_smul, hkNorm]
    exact inv_mul_cancel₀ hJ.ne'
  have hupper : ∀ z ∈ closedBall 0 (5 * R), ‖f z‖ ≤ Real.exp (R * (5 * M)) := by
    intro z hz
    have hg := convex_solution_norm_upper (convex_closedBall (0 : ℂ) (5 * R)) hode hA
      (mem_closedBall_self (by positivity)) hz
    have hzN : ‖z‖ ≤ 5 * R := mem_closedBall_zero_iff.mp hz
    have hscalar : ‖v z‖ ≤ J * Real.exp (M * (5 * R)) :=
      (norm_scalar_le_jet hn v z).trans (hg.trans (by
        simp only [sub_zero]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hzN hM)) hJ.le))
    change ‖k * v z‖ ≤ _
    rw [norm_mul, hkNorm]
    calc
      _ ≤ J⁻¹ * (J * Real.exp (M * (5 * R))) :=
        mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr hJ.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul]; congr 1; ring
  have hsmall : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    hf.mono (closedBall_subset_closedBall (by linarith))
  obtain ⟨z, hz, hsample⟩ := ScalarCauchyNoncollapse.exists_scalar_sample
    (n := n) (x := 0) (δ := 1) hR (by norm_num)
    (by simpa only [mul_zero, mul_one] using hsmall)
  rw [mul_zero, hfjet] at hsample
  have haz : (R : ℂ) * z ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hRp.le).trans_eq (mul_one R)
  have hCp : 0 < cauchyConstant n 1 := cauchyConstant_pos (by norm_num)
  have hCl : 0 ≤ Real.log (cauchyConstant n 1) := Real.log_nonneg (cauchyConstant_one_ge_one n)
  have hlower : Real.exp (-R * Real.log (cauchyConstant n 1)) ≤ ‖f ((R : ℂ) * z)‖ := by
    calc
      _ ≤ Real.exp (-Real.log (cauchyConstant n 1)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (cauchyConstant n 1)⁻¹ := by rw [Real.exp_neg, Real.exp_log hCp]
      _ ≤ _ := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ hCp).mpr
        simpa only [mul_comm] using hsample
  have hj := moving_center_divisor_mass_le hRp hRp (mul_nonneg (by norm_num) hM)
    haz hf hupper hlower
  have hmono := divisor_sum_mono
    (closedBall_subset_closedBall (by linarith : R ≤ 2 * R))
    (hf.mono (closedBall_subset_closedBall (by linarith : 2 * R ≤ 5 * R)))
  have hJsmall : ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) / R ≤
      (5 * M + Real.log (cauchyConstant n 1)) / Real.log (4 / 3 : ℝ) :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hmono) hRp.le).trans hj
  have hc : (5 * M + Real.log (cauchyConstant n 1)) / Real.log (4 / 3 : ℝ) ≤
      diskCountConstant n M := by
    unfold diskCountConstant
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num))
  have he : MeromorphicOn.divisor f (closedBall 0 R) = MeromorphicOn.divisor v (closedBall 0 R) := by
    ext z
    exact divisor_const_mul (hv.mono (closedBall_subset_closedBall (by linarith))) hk z
  rw [he] at hJsmall
  exact (div_le_iff₀ hRp).mp (hJsmall.trans hc)

/-- Explicit operator bound for the actual companion matrix. -/
theorem companion_norm_le {n : ℕ} {b : Fin (n + 1) → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ j, ‖b j‖ ≤ B) :
    ‖CompanionObservation.companion b‖ ≤ 1 + (n + 1 : ℝ) * B := by
  have hM : 0 ≤ 1 + (n + 1 : ℝ) * B := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro y
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg y))).mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [CompanionObservation.companion_last, norm_neg]
    calc
      _ ≤ ∑ j : Fin (n + 1), ‖b j * y j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (n + 1), B * ‖y‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hb j) (norm_le_pi_norm y j) (norm_nonneg _) hB
      _ = ((n + 1 : ℝ) * B) * ‖y‖ := by simp; ring
      _ ≤ _ := by nlinarith [norm_nonneg y]
  · have hj : ‖CompanionObservation.companion b y j.castSucc‖ ≤ ‖y‖ := by
      simpa [CompanionObservation.companion] using norm_le_pi_norm y j.succ
    exact hj.trans (by nlinarith [norm_nonneg y, mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) hB])

/-- A bounded monic scalar equation gives a solution-independent linear
zero count. Neither the coefficient bound nor the count is normalized away. -/
theorem disk_divisor_le_of_scalar_ode {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hv : AnalyticOnNhd ℂ v (closedBall 0 (5 * R)))
    (hscalar : ∀ z ∈ closedBall 0 (5 * R), iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hb : ∀ z ∈ closedBall 0 (5 * R), ∀ j, ‖b z j‖ ≤ B)
    (hne : jet (n + 1) v 0 ≠ 0) :
    ((∑ᶠ z, MeromorphicOn.divisor v (closedBall 0 R) z : ℤ) : ℝ) ≤
      diskCountConstant (n + 1) (1 + (n + 1 : ℝ) * B) * R := by
  exact disk_divisor_le_of_jet_ode (by omega) hR (by positivity) hv
    (fun z hz => ScalarCompanionODE.jet_hasDerivAt_companion (hv z hz) (b z) (hscalar z hz))
    (fun z hz => companion_norm_le hB (hb z hz)) hne

#print axioms disk_divisor_le_of_jet_ode
#print axioms disk_divisor_le_of_scalar_ode
end V10.BoundedCoefficientZeroCount
