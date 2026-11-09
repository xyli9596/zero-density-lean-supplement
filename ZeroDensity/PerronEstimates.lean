import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Actual norm-growth bounds for linear differential equations. These estimates
support the bounded-solution reduction and local logarithmic equicontinuity in
Perron's theorem; they do not classify growth by eigenvalues. -/
noncomputable section
namespace ZeroDensity.PerronEstimates
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gronwall's exponential bound for an actual bounded-operator ODE. -/
theorem solution_norm_upper {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a b K : ℝ}
    (hab : a ≤ b) (hode : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) :
    ‖x b‖ ≤ ‖x a‖ * Real.exp (K*(b-a)) := by
  have hc : ContinuousOn x (Icc a b) := fun t ht =>
    (hode t ht).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt x (A t (x t)) (Ici t) t :=
    fun t ht => (hode t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  have hn : ∀ t ∈ Ico a b, ‖A t (x t)‖ ≤ K*‖x t‖+0 := by
    intro t ht
    simpa only [add_zero] using (A t).le_opNorm (x t) |>.trans
      (mul_le_mul_of_nonneg_right (hA t ⟨ht.1,ht.2.le⟩) (norm_nonneg _))
  simpa only [gronwallBound_ε0] using
    norm_le_gronwallBound_of_norm_deriv_right_le hc hd le_rfl hn b ⟨hab,le_rfl⟩

/-- The backward bound follows from the same ODE under time reversal. -/
theorem solution_norm_backward {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a b K : ℝ}
    (hab : a ≤ b) (hode : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) :
    ‖x a‖ ≤ ‖x b‖ * Real.exp (K*(b-a)) := by
  let y : ℝ → E := fun t => x (a+b-t)
  let C : ℝ → E →L[ℝ] E := fun t => -A (a+b-t)
  have hd : ∀ t ∈ Icc a b, HasDerivAt y (C t (y t)) t := by
    intro t ht
    have hm : a+b-t ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hh := (hode _ hm).scomp t ((hasDerivAt_const t (a+b)).sub (hasDerivAt_id t))
    simpa [y,C, Function.comp_def] using hh
  have hC : ∀ t ∈ Icc a b, ‖C t‖ ≤ K := by
    intro t ht
    simpa [C] using hA (a+b-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa [y] using solution_norm_upper hab hd hC

/-- A nonzero initial value cannot reach zero while solving the linear ODE. -/
theorem solution_ne_zero {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a b K : ℝ}
    (hab : a ≤ b) (hode : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) (ha : x a ≠ 0) : x b ≠ 0 := by
  intro hz
  have hh := solution_norm_backward hab hode hA
  rw [hz,norm_zero,zero_mul] at hh
  exact (norm_pos_iff.mpr ha).not_ge hh

/-- Logarithmic norm is Lipschitz on every interval with bounded coefficients.
This directly applies to scaled holomorphic derivative vectors on segments. -/
theorem solution_log_norm_bound {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a b K : ℝ}
    (hab : a ≤ b) (hode : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) (ha : x a ≠ 0) :
    |Real.log ‖x b‖-Real.log ‖x a‖| ≤ K*(b-a) := by
  have hb := solution_ne_zero hab hode hA ha
  have hu := Real.log_le_log (norm_pos_iff.mpr hb) (solution_norm_upper hab hode hA)
  have hl := Real.log_le_log (norm_pos_iff.mpr ha) (solution_norm_backward hab hode hA)
  rw [Real.log_mul (norm_ne_zero_iff.mpr ha) (Real.exp_ne_zero _),Real.log_exp] at hu
  rw [Real.log_mul (norm_ne_zero_iff.mpr hb) (Real.exp_ne_zero _),Real.log_exp] at hl
  rw [abs_le]
  constructor <;> linarith

/-- The scalar exponential shift used to reduce Perron's theorem to bounded
solutions. The shift is anchored at the initial time, which changes no rate. -/
def shiftedSolution (c a : ℝ) (x : ℝ → E) (t : ℝ) : E :=
  Real.exp (-c*(t-a)) • x t

/-- Boundedness follows directly from the actual ODE, not from an assumed
exponential bound on its solution. -/
theorem shiftedSolution_norm_le {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a t K c : ℝ}
    (hat : a ≤ t) (hode : ∀ s ∈ Icc a t, HasDerivAt x (A s (x s)) s)
    (hA : ∀ s ∈ Icc a t, ‖A s‖ ≤ K) (hshift : K ≤ c) :
    ‖shiftedSolution c a x t‖ ≤ ‖x a‖ := by
  have hb := solution_norm_upper hat hode hA
  rw [shiftedSolution,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-c*(t-a)) * (‖x a‖*Real.exp (K*(t-a))) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ‖x a‖ * Real.exp ((K-c)*(t-a)) := by
      have he : (K-c)*(t-a) = -c*(t-a)+K*(t-a) := by ring
      rw [he,Real.exp_add]
      ring
    _ ≤ ‖x a‖ * 1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hshift) (sub_nonneg.mpr hat))) (norm_nonneg _)
    _ = _ := mul_one _

/-- Exact shifted differential equation, valid for any bounded-operator system. -/
theorem shiftedSolution_hasDerivAt {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a t c : ℝ}
    (hode : HasDerivAt x (A t (x t)) t) :
    HasDerivAt (shiftedSolution c a x)
      ((A t - c • ContinuousLinearMap.id ℝ E) (shiftedSolution c a x t)) t := by
  have hs : HasDerivAt (fun s : ℝ => Real.exp (-c*(s-a)))
      (Real.exp (-c*(t-a))*(-c)) t := by
    simpa using (((hasDerivAt_id t).sub_const a).const_mul (-c)).exp
  have hh := hs.smul hode
  convert hh using 1
  · rfl
  · simp only [shiftedSolution, sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
    module

/-- Quantitative finite-time stability from actual operator perturbations.
The reference trajectory solves its own ODE; its error is computed rather
than supplied as a presumed solution-difference estimate. -/
theorem solution_difference_bound {A C : ℝ → E →L[ℝ] E} {x z : ℝ → E}
    {a b K ε M : ℝ} (hab : a ≤ b) (hε : 0 ≤ ε)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (A t (x t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (C t (z t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (hAC : ∀ t ∈ Icc a b, ‖A t-C t‖ ≤ ε)
    (hzn : ∀ t ∈ Icc a b, ‖z t‖ ≤ M) :
    ‖x b-z b‖ ≤ gronwallBound ‖x a-z a‖ K (ε*M) (b-a) := by
  have hc : ContinuousOn (fun t => x t-z t) (Icc a b) := fun t ht =>
    ((hx t ht).sub (hz t ht)).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => x t-z t)
      (A t (x t)-C t (z t)) (Ici t) t := by
    intro t ht
    exact ((hx t ⟨ht.1,ht.2.le⟩).sub (hz t ⟨ht.1,ht.2.le⟩)).hasDerivWithinAt
  have hn : ∀ t ∈ Ico a b,
      ‖A t (x t)-C t (z t)‖ ≤ K*‖x t-z t‖+ε*M := by
    intro t ht
    have htc : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    have he : A t (x t)-C t (z t) = A t (x t-z t)+(A t-C t) (z t) := by
      simp only [map_sub, sub_apply]
      abel
    rw [he]
    calc
      _ ≤ ‖A t (x t-z t)‖+‖(A t-C t) (z t)‖ := norm_add_le _ _
      _ ≤ K*‖x t-z t‖+ε*‖z t‖ := add_le_add
        ((A t).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hA t htc) (norm_nonneg _)))
        ((A t-C t).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hAC t htc) (norm_nonneg _)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hzn t htc) hε)
  exact norm_le_gronwallBound_of_norm_deriv_right_le hc hd le_rfl hn b ⟨hab,le_rfl⟩

/-- Uniform finite-time convergence of actual ODE trajectories from uniform
coefficient convergence and a shared initial value. This is the fundamental
matrix convergence step used by the scalar/jet observation argument. -/
theorem solutions_uniformly_of_small_coefficients {ι : Type*} {l : Filter ι}
    {A : ι → ℝ → E →L[ℝ] E} {C : ℝ → E →L[ℝ] E}
    {x : ι → ℝ → E} {z : ℝ → E} {a b K M : ℝ} {ε : ι → ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hx : ∀ r, ∀ t ∈ Icc a b, HasDerivAt (x r) (A r t (x r t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (C t (z t)) t)
    (hinit : ∀ r, x r a = z a)
    (hA : ∀ᶠ r in l, ∀ t ∈ Icc a b, ‖A r t‖ ≤ K)
    (hAC : ∀ᶠ r in l, ∀ t ∈ Icc a b, ‖A r t-C t‖ ≤ ε r)
    (hε : ∀ᶠ r in l, 0 ≤ ε r) (hεlim : Tendsto ε l (𝓝 0))
    (hzn : ∀ t ∈ Icc a b, ‖z t‖ ≤ M) :
    TendstoUniformlyOn x z l (Icc a b) := by
  have hg : Tendsto (fun r => gronwallBound 0 K (ε r*M) (b-a)) l (𝓝 0) := by
    have hh := ((gronwallBound_continuous_ε 0 K (b-a)).tendsto (0*M)).comp (hεlim.mul_const M)
    simpa only [zero_mul,gronwallBound_ε0_δ0,Function.comp_def] using hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hA,hAC,hε,hg.eventually (gt_mem_nhds hδ)] with r hrA hrAC hrε hrδ
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hh := solution_difference_bound ht.1 hrε
    (fun s hs => hx r s (hsub hs)) (fun s hs => hz s (hsub hs))
    (fun s hs => hrA s (hsub hs)) (fun s hs => hrAC s (hsub hs))
    (fun s hs => hzn s (hsub hs))
  rw [hinit r,sub_self,norm_zero] at hh
  have hm := gronwallBound_mono (δ := 0) le_rfl (mul_nonneg hrε hM) hK
    (sub_le_sub_right ht.2 a)
  rw [dist_comm,dist_eq_norm]
  exact (hh.trans hm).trans_lt hrδ

/-- Uniform coefficient convergence suffices for uniform finite-time trajectory
convergence; an error envelope is not an additional input. -/
theorem solutions_uniformly_of_coefficients {ι : Type*} {l : Filter ι}
    {A : ι → ℝ → E →L[ℝ] E} {C : ℝ → E →L[ℝ] E}
    {x : ι → ℝ → E} {z : ℝ → E} {a b K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hx : ∀ r, ∀ t ∈ Icc a b, HasDerivAt (x r) (A r t (x r t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (C t (z t)) t)
    (hinit : ∀ r, x r a = z a)
    (hA : ∀ᶠ r in l, ∀ t ∈ Icc a b, ‖A r t‖ ≤ K)
    (hcoeff : TendstoUniformlyOn A C l (Icc a b))
    (hzn : ∀ t ∈ Icc a b, ‖z t‖ ≤ M) :
    TendstoUniformlyOn x z l (Icc a b) := by
  have heps : Tendsto (fun m : ℕ => (1:ℝ)/(m+1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1).comp (tendsto_add_atTop_nat 1)
  have hg : Tendsto (fun m : ℕ => gronwallBound 0 K (((1:ℝ)/(m+1))*M) (b-a))
      atTop (𝓝 0) := by
    have hh := ((gronwallBound_continuous_ε 0 K (b-a)).tendsto (0*M)).comp (heps.mul_const M)
    simpa only [zero_mul,gronwallBound_ε0_δ0,Function.comp_def] using hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨m,hm⟩ := (hg.eventually (gt_mem_nhds hδ)).exists
  let ε : ℝ := 1/(m+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hcoeff) ε hε
  filter_upwards [hA,hclose] with r hrA hrclose
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hh := solution_difference_bound ht.1 hε.le
    (fun s hs => hx r s (hsub hs)) (fun s hs => hz s (hsub hs))
    (fun s hs => hrA s (hsub hs)) (fun s hs => by
      have hh := hrclose s (hsub hs)
      rw [dist_comm,dist_eq_norm] at hh
      exact hh.le)
    (fun s hs => hzn s (hsub hs))
  rw [hinit r,sub_self,norm_zero] at hh
  have hmono := gronwallBound_mono (δ := 0) le_rfl (mul_nonneg hε.le hM) hK
    (sub_le_sub_right ht.2 a)
  rw [dist_comm,dist_eq_norm]
  exact (hh.trans hmono).trans_lt hm

#print axioms solutions_uniformly_of_coefficients
#print axioms solutions_uniformly_of_small_coefficients
#print axioms solution_difference_bound
#print axioms shiftedSolution_norm_le
#print axioms shiftedSolution_hasDerivAt
#print axioms solution_norm_upper
#print axioms solution_norm_backward
#print axioms solution_ne_zero
#print axioms solution_log_norm_bound
end ZeroDensity.PerronEstimates
