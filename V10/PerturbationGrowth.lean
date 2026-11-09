import V10.ExponentialType
import Mathlib.Tactic

/-! The original strict exponential-type hypothesis in Theorem 1.5 yields
a genuine global coefficient bound. The extended-real type is retained until
its finiteness has been proved. A finite family admits one strict rate gap
and one global constant, both independent of the argument and solution. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace V10.PerturbationGrowth
open ExponentialType

/-- Converse direction needed for the perturbation theorem: a strict type
bound, rather than an already supplied pointwise bound, controls every point. -/
theorem global_bound_of_type_lt {f : ℂ → ℂ} (hf : Continuous f) {σ : ℝ}
    (hσ : 0 < σ) (ht : typeOne f < (σ : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖) := by
  have he : ∀ᶠ r : ℝ in atTop,
      ((logPlus (diskMax f r) / r : ℝ) : EReal) < (σ : EReal) :=
    eventually_lt_of_limsup_lt ht
  obtain ⟨T, hT⟩ := eventually_atTop.mp he
  let R := max 1 T
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let C := max 1 (diskMax f R)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : ‖z‖ ≤ R
  · have hn : ‖f z‖ ≤ C :=
      (norm_le_diskMax hf (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans
        (le_max_right _ _)
    have hexp : 1 ≤ Real.exp (σ * ‖z‖) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hσ.le (norm_nonneg z))
    exact hn.trans (by nlinarith)
  · have hr : 0 < ‖z‖ := hR.trans (lt_of_not_ge hz)
    have hprof : logPlus (diskMax f ‖z‖) / ‖z‖ < σ :=
      EReal.coe_lt_coe_iff.mp (hT ‖z‖ ((le_max_right _ _).trans (le_of_not_ge hz)))
    have hlog : Real.log (max 1 (diskMax f ‖z‖)) ≤ σ * ‖z‖ :=
      ((div_lt_iff₀ hr).mp hprof).le
    have hm : max 1 (diskMax f ‖z‖) ≤ Real.exp (σ * ‖z‖) :=
      (Real.log_le_iff_le_exp (zero_lt_one.trans_le (le_max_left _ _))).mp hlog
    have hn : ‖f z‖ ≤ Real.exp (σ * ‖z‖) :=
      (norm_le_diskMax hf (by simp)).trans ((le_max_right _ _).trans hm)
    exact hn.trans (by have h1 : 1 ≤ C := le_max_left _ _; nlinarith [Real.exp_pos (σ * ‖z‖)])

theorem global_bound_of_circle_type_lt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {σ : ℝ} (hσ : 0 < σ)
    (ht : typeOneSphere f < (σ : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (σ * ‖z‖) := by
  rw [typeOneSphere_eq_typeOne hf] at ht
  exact global_bound_of_type_lt
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hf).continuous hσ ht

/-- One rate b<a and one constant work for all finitely many entire
perturbation coefficients. Here q is the actual positive differential-order gap. -/
theorem finite_family_growth {ι : Type*} [Fintype ι] [Nonempty ι]
    {R : ι → ℂ → ℂ} {q : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (hR : ∀ i, AnalyticOnNhd ℂ (R i) univ) (hq : ∀ i, 0 < q i)
    (ht : ∀ i, typeOneSphere (R i) < ((q i * a : ℝ) : EReal)) :
    ∃ b C : ℝ, 0 < b ∧ b < a ∧ 0 < C ∧
      ∀ i z, ‖R i z‖ ≤ C * Real.exp (q i * b * ‖z‖) := by
  classical
  have hreal (i : ι) : ((typeOneSphere (R i)).toReal : EReal) = typeOneSphere (R i) := by
    apply EReal.coe_toReal
    · exact ne_top_of_lt (ht i)
    · exact ne_bot_of_le_ne_bot (by simp) (typeOneSphere_nonneg (R i))
  let t : ι → ℝ := fun i => (typeOneSphere (R i)).toReal / q i
  have hta (i : ι) : t i < a := by
    apply (div_lt_iff₀ (hq i)).mpr
    have ht' := ht i
    rw [← hreal i] at ht'
    simpa only [mul_comm] using EReal.coe_lt_coe_iff.mp ht'
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty t
  have hMa : M < a := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hta i)
  let b : ℝ := (max 0 M + a) / 2
  have hmax : max 0 M < a := max_lt ha hMa
  have hb : 0 < b := by dsimp [b]; linarith [le_max_left (0 : ℝ) M]
  have hba : b < a := by dsimp [b]; linarith
  have hMb : M < b := by dsimp [b]; linarith [le_max_right (0 : ℝ) M]
  have htb (i : ι) : typeOneSphere (R i) < ((q i * b : ℝ) : EReal) := by
    rw [← hreal i]
    apply EReal.coe_lt_coe_iff.mpr
    have hi : t i < b := (Finset.le_sup' t (Finset.mem_univ i)).trans_lt hMb
    have hh := (div_lt_iff₀ (hq i)).mp hi
    simpa only [mul_comm] using hh
  choose C hC hbound using fun i => global_bound_of_circle_type_lt
    (hR i) (mul_pos (hq i) hb) (htb i)
  let C₀ : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hC₀ : 0 < C₀ := (hC (Classical.arbitrary ι)).trans_le
    (Finset.le_sup' C (Finset.mem_univ _))
  refine ⟨b, C₀, hb, hba, hC₀, ?_⟩
  intro i z
  exact (hbound i z).trans (mul_le_mul_of_nonneg_right
    (Finset.le_sup' C (Finset.mem_univ i)) (Real.exp_pos _).le)

#print axioms global_bound_of_circle_type_lt
#print axioms finite_family_growth
end V10.PerturbationGrowth
