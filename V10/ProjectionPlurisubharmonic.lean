import V10.PluriPotentialSeries
import Mathlib.Tactic

/-!
# Actual logarithmic projection poles on coefficient balls

The deficit M - log |F(c)| is a nonnegative plurisuperharmonic function
where |F(c)| ≤ exp M. At an actual zero of F its value is infinity.
The proof derives it by monotone convergence of actual truncated analytic
logarithms. No plurisubharmonicity or supermean assertion is an input.
-/

noncomputable section
open Set Metric
open scoped Topology NNReal ENNReal
namespace V10.ProjectionPlurisubharmonic
open PluriPotentialSeries

theorem maxLog_mono_cutoff {a b x : ℝ} (hab : a ≤ b) : maxLog a x ≤ maxLog b x := by
  unfold maxLog
  exact Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _))
    (max_le_max (Real.exp_le_exp.mpr hab) le_rfl)

theorem log_le_maxLog {b x : ℝ} (hx : 0 < x) : Real.log x ≤ maxLog b x := by
  unfold maxLog
  exact Real.log_le_log hx (le_max_right _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def logDeficit (F : E →L[ℂ] ℂ) (M : ℝ) (c : E) : ℝ≥0∞ :=
  if F c = 0 then ∞ else ENNReal.ofReal (M - Real.log ‖F c‖)

theorem logDeficit_eq_iSup (F : E →L[ℂ] ℂ) {M : ℝ} (hM : 0 ≤ M) (c : E) :
    logDeficit F M c = ⨆ n : ℕ, ENNReal.ofReal (M - maxLog (-(n : ℝ)) ‖F c‖) := by
  by_cases hc : F c = 0
  · simp only [logDeficit, hc, if_pos, norm_zero,
      maxLog_eq_b (Real.exp_pos _).le, sub_neg_eq_add]
    symm
    apply top_le_iff.mp
    rw [← ENNReal.iSup_natCast]
    apply iSup_le
    intro n
    apply le_trans _ (le_iSup (fun k : ℕ => ENNReal.ofReal (M + k)) n)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [logDeficit, if_neg hc]
    have hp : 0 < ‖F c‖ := norm_pos_iff.mpr hc
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ‖F c‖)
      have he : Real.exp (-(n : ℝ)) ≤ ‖F c‖ := by
        rw [← Real.exp_log hp]
        apply Real.exp_le_exp.mpr
        linarith
      have hh := le_iSup (fun k : ℕ => ENNReal.ofReal (M - maxLog (-(k : ℝ)) ‖F c‖)) n
      rwa [maxLog_eq_log he] at hh
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (log_le_maxLog hp) M)

theorem logDeficit_plurisuperharmonic (F : E →L[ℂ] ℂ) {U : Set E} (hU : IsOpen U)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ c ∈ U, ‖F c‖ ≤ Real.exp M) :
    PlurisuperharmonicOn (logDeficit F M) U := by
  have he : logDeficit F M = fun c =>
      ⨆ n : ℕ, ENNReal.ofReal (M - maxLog (-(n : ℝ)) ‖F c‖) :=
    funext (logDeficit_eq_iSup F hM)
  rw [he]
  apply PlurisuperharmonicOn.iSup
  · intro n
    exact truncated_linear_log F hU ((neg_nonpos.mpr (Nat.cast_nonneg n)).trans hM) hbound
  · intro n m hnm c
    apply ENNReal.ofReal_le_ofReal
    apply sub_le_sub_left
    apply maxLog_mono_cutoff
    exact neg_le_neg (by exact_mod_cast hnm)

theorem logDeficit_eq_top_iff (F : E →L[ℂ] ℂ) (M : ℝ) (c : E) :
    logDeficit F M c = ∞ ↔ F c = 0 := by
  simp only [logDeficit]
  split_ifs with h <;> simp [h]

/-- The actual normalized logarithmic pole is upper semicontinuous, has no
positive infinity, and has pole set exactly the functional's zero set. -/
theorem negative_logDeficit_properties (F : E →L[ℂ] ℂ) {U : Set E} (hU : IsOpen U)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ c ∈ U, ‖F c‖ ≤ Real.exp M) :
    UpperSemicontinuousOn (negativePotential (logDeficit F M)) U ∧
    (∀ c, negativePotential (logDeficit F M) c ≠ ⊤) ∧
    (∀ c, negativePotential (logDeficit F M) c = ⊥ ↔ F c = 0) := by
  refine ⟨negativePotential_upperSemicontinuous
    (logDeficit_plurisuperharmonic F hU hM hbound).lowerSemicontinuousOn,
    negativePotential_ne_top _, ?_⟩
  intro c
  rw [negativePotential_eq_bot, logDeficit_eq_top_iff]

#print axioms logDeficit_plurisuperharmonic
#print axioms negative_logDeficit_properties
end V10.ProjectionPlurisubharmonic
