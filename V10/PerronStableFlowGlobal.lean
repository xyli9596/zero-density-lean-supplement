import V10.PerronStableFlowUniqueness

/-! Actual half-line IVP existence for complex finite-dimensional systems.
This is a scalar-restriction wrapper around the proved Picard construction
on compatible compact intervals, with interior-only endpoint regularity. -/
namespace V10.PerronStableFlow
open Set Module
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Every initial value is realized by a genuine solution on the entire
closed half-line. No global bound, fundamental matrix, or assumed solution
family is supplied. -/
theorem exists_solution_halfline {T : ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Ici T)) (v : E) :
    ∃ u : ℝ → E, u T = v ∧ ContinuousOn u (Ici T) ∧
      ∀ t > T, HasDerivAt u (A t (u t)) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let r := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  have hc : ContinuousOn (fun t => (A t).restrictScalars ℝ) (Ici T) :=
    r.continuous.comp_continuousOn hA
  exact WasowFuchsianODE.exists_solution_Ici _ hc v

/-- The actual half-line IVP has a unique trajectory on its stated domain. -/
theorem exists_unique_solution_halfline {T : ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Ici T)) (v : E) :
    ∃ u : ℝ → E, u T = v ∧ ContinuousOn u (Ici T) ∧
      (∀ t > T, HasDerivAt u (A t (u t)) t) ∧
      ∀ w : ℝ → E, w T = v → ContinuousOn w (Ici T) →
        (∀ t > T, HasDerivAt w (A t (w t)) t) → EqOn u w (Ici T) := by
  obtain ⟨u, huT, huc, hud⟩ := exists_solution_halfline A hA v
  refine ⟨u, huT, huc, hud, ?_⟩
  intro w hwT hwc hwd
  exact solution_eqOn_halfline A hA huc hwc hud hwd (huT.trans hwT.symm)

#print axioms exists_solution_halfline
#print axioms exists_unique_solution_halfline
end
end V10.PerronStableFlow
