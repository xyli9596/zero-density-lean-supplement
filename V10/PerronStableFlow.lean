import WasowFuchsianODE
import ZeroDensity.PerronEstimates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Actual finite-time linear flow for the stable initial-value subspace

Solutions are constructed by the existing Picard fixed-point proof for the
actual continuous coefficient. Uniqueness gives complex linearity, backward
Gronwall gives injectivity, and finite dimensionality gives invertibility.
No flow, inverse solution, or invertible fundamental matrix is assumed.
-/

namespace V10.PerronStableFlow
open Set Filter Module
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A genuine solution on the whole compact interval with prescribed initial
value, including the actual ODE derivative at both endpoints. -/
theorem exists_solution {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (x : E) :
    ∃ u : ℝ → E, Continuous u ∧ u a = x ∧
      ∀ t ∈ Icc a b, HasDerivAt u (A t (u t)) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let r := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  have hc : ContinuousOn (fun t => (A t).restrictScalars ℝ) (Icc a b) :=
    r.continuous.comp_continuousOn hA
  exact WasowFuchsianODE.exists_solution_Icc hab _ hc x

/-- A chosen actual Picard solution, used only through existence and uniqueness. -/
def solution {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (x : E) : ℝ → E :=
  (exists_solution hab A hA x).choose

theorem solution_spec {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (x : E) :
    Continuous (solution hab A hA x) ∧ solution hab A hA x a = x ∧
      ∀ t ∈ Icc a b, HasDerivAt (solution hab A hA x)
        (A t (solution hab A hA x t)) t :=
  (exists_solution hab A hA x).choose_spec

omit [FiniteDimensional ℂ E] in
/-- Actual solutions with the same initial value agree on the compact interval. -/
theorem solution_eqOn {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) {u v : ℝ → E}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (A t (u t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (A t (v t)) t)
    (hi : u a = v a) : EqOn u v (Icc a b) := by
  let r := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  exact WasowFuchsianODE.solution_eqOn_Icc hab (fun t => (A t).restrictScalars ℝ)
    (r.continuous.comp_continuousOn hA) u v hu hv hi

theorem solution_add {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (x y : E) :
    EqOn (solution hab A hA (x + y))
      (fun t => solution hab A hA x t + solution hab A hA y t) (Icc a b) := by
  apply solution_eqOn hab A hA (solution_spec hab A hA (x + y)).2.2
  · intro t ht
    have hh := ((solution_spec hab A hA x).2.2 t ht).add
      ((solution_spec hab A hA y).2.2 t ht)
    change HasDerivAt (fun t => solution hab A hA x t + solution hab A hA y t)
      (A t (solution hab A hA x t) + A t (solution hab A hA y t)) t at hh
    simpa only [map_add] using hh
  · rw [(solution_spec hab A hA (x + y)).2.1,
      (solution_spec hab A hA x).2.1, (solution_spec hab A hA y).2.1]

theorem solution_smul {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (c : ℂ) (x : E) :
    EqOn (solution hab A hA (c • x))
      (fun t => c • solution hab A hA x t) (Icc a b) := by
  apply solution_eqOn hab A hA (solution_spec hab A hA (c • x)).2.2
  · intro t ht
    have hh := ((solution_spec hab A hA x).2.2 t ht).const_smul c
    change HasDerivAt (fun t => c • solution hab A hA x t)
      (c • A t (solution hab A hA x t)) t at hh
    simpa only [map_smul] using hh
  · rw [(solution_spec hab A hA (c • x)).2.1, (solution_spec hab A hA x).2.1]

/-- The true endpoint solution map is complex linear. -/
def flowLinearMap {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) : E →ₗ[ℂ] E where
  toFun x := solution hab A hA x b
  map_add' x y := solution_add hab A hA x y ⟨hab, le_rfl⟩
  map_smul' c x := solution_smul hab A hA c x ⟨hab, le_rfl⟩

/-- Vanishing at the final time forces the initial value to vanish, by a
backward estimate for the actual constructed solution. -/
theorem flow_eq_zero_iff {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (x : E) :
    flowLinearMap hab A hA x = 0 ↔ x = 0 := by
  constructor
  · intro hz
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
    have hb := ZeroDensity.PerronEstimates.solution_norm_backward
      (A := fun t => (A t).restrictScalars ℝ) hab
      (solution_spec hab A hA x).2.2
      (fun t ht => by simpa only [ContinuousLinearMap.norm_restrictScalars] using hK t ht)
    rw [(solution_spec hab A hA x).2.1] at hb
    change solution hab A hA x b = 0 at hz
    rw [hz, norm_zero, zero_mul] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg x))
  · rintro rfl
    exact map_zero _

theorem flow_injective {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) : Function.Injective (flowLinearMap hab A hA) := by
  intro x y hxy
  have hz : flowLinearMap hab A hA (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp ((flow_eq_zero_iff hab A hA (x - y)).mp hz)

/-- The actual finite-time solution map is invertible, obtained from proved
injectivity in finite dimension rather than an assumed fundamental matrix. -/
def flowLinearEquiv {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) : E ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (flowLinearMap hab A hA)
    ⟨flow_injective hab A hA, LinearMap.surjective_of_injective (flow_injective hab A hA)⟩

/-- Transporting a tail initial-value space to the original time preserves
its complex dimension. The map is the actual ODE flow just constructed. -/
theorem flow_pullback_finrank {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (W : Submodule ℂ E) :
    finrank ℂ (W.map (flowLinearEquiv hab A hA).symm.toLinearMap) = finrank ℂ W :=
  (flowLinearEquiv hab A hA).symm.finrank_map_eq W

/-- Membership in the transported space is exactly membership of the actual
terminal state in the tail space. -/
theorem mem_flow_pullback_iff {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) (W : Submodule ℂ E) (x : E) :
    x ∈ W.map (flowLinearEquiv hab A hA).symm.toLinearMap ↔
      flowLinearMap hab A hA x ∈ W := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change flowLinearEquiv hab A hA ((flowLinearEquiv hab A hA).symm y) ∈ W
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  · intro hx
    refine ⟨flowLinearEquiv hab A hA x, hx, ?_⟩
    exact (flowLinearEquiv hab A hA).symm_apply_apply x

#print axioms exists_solution
#print axioms flow_injective
#print axioms flowLinearEquiv
#print axioms flow_pullback_finrank
#print axioms mem_flow_pullback_iff
end
end V10.PerronStableFlow
