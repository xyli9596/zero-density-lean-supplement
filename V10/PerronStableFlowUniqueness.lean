import V10.PerronStableFlow

/-! Initial-value uniqueness with a continuous initial boundary and only
interior ODE derivatives. This applies to the clamped half-line fixed point. -/
namespace V10.PerronStableFlow
open Set Filter Module
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Gronwall's bound does not require an ordinary derivative at the initial
boundary. It follows by approaching that boundary from the interior. -/
theorem solution_norm_upper_interior {A : ℝ → E →L[ℂ] E} {u : ℝ → E} {a b K : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (Icc a b))
    (hode : ∀ t ∈ Ioc a b, HasDerivAt u (A t (u t)) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) :
    ‖u b‖ ≤ ‖u a‖ * Real.exp (K * (b - a)) := by
  obtain rfl | hab := hab.eq_or_lt
  · simp
  have hb : ∀ s ∈ Ioo a b, ‖u b‖ ≤ ‖u s‖ * Real.exp (K * (b - s)) := by
    intro s hs
    apply ZeroDensity.PerronEstimates.solution_norm_upper
      (A := fun t => (A t).restrictScalars ℝ) hs.2.le
    · intro t ht
      exact hode t ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩
    · intro t ht
      simpa only [ContinuousLinearMap.norm_restrictScalars] using
        hA t ⟨le_trans hs.1.le ht.1, ht.2⟩
  apply ContinuousWithinAt.closure_le (s := Ioo a b) (x := a) ?_
    continuousWithinAt_const ?_ hb
  · rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  · have hc : ContinuousWithinAt u (Ioo a b) a :=
      (hu a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
    exact hc.norm.mul (by fun_prop)

/-- Two actual solutions with a common continuous initial value agree,
even when only derivatives strictly after that initial time are available. -/
theorem solution_eqOn_interior {a b : ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) {u v : ℝ → E}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioc a b, HasDerivAt u (A t (u t)) t)
    (hdv : ∀ t ∈ Ioc a b, HasDerivAt v (A t (v t)) t)
    (hi : u a = v a) : EqOn u v (Icc a b) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  intro t ht
  have hh := solution_norm_upper_interior (A := A) (u := fun s => u s - v s)
    ht.1 ((hu.sub hv).mono (Icc_subset_Icc_right ht.2))
    (fun s hs => by
      have hd := (hdu s ⟨hs.1, hs.2.trans ht.2⟩).sub (hdv s ⟨hs.1, hs.2.trans ht.2⟩)
      change HasDerivAt (fun s => u s - v s) (A s (u s) - A s (v s)) s at hd
      simpa only [map_sub] using hd)
    (fun s hs => hK s ⟨hs.1, hs.2.trans ht.2⟩)
  rw [hi, sub_self, norm_zero, zero_mul] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- Half-line uniqueness in the exact regularity class of a Volterra solution. -/
theorem solution_eqOn_halfline {a : ℝ} (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Ici a)) {u v : ℝ → E}
    (hu : ContinuousOn u (Ici a)) (hv : ContinuousOn v (Ici a))
    (hdu : ∀ t > a, HasDerivAt u (A t (u t)) t)
    (hdv : ∀ t > a, HasDerivAt v (A t (v t)) t)
    (hi : u a = v a) : EqOn u v (Ici a) := by
  intro t ht
  exact solution_eqOn_interior A (hA.mono Icc_subset_Ici_self)
    (hu.mono Icc_subset_Ici_self) (hv.mono Icc_subset_Ici_self)
    (fun s hs => hdu s hs.1) (fun s hs => hdv s hs.1) hi ⟨ht, le_rfl⟩

/-- The actual finite-time flow agrees with any continuous solution having
only interior derivatives. -/
theorem flow_apply_eq_of_solution_interior [FiniteDimensional ℂ E]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℂ] E)
    (hA : ContinuousOn A (Icc a b)) {u : ℝ → E}
    (hu : ContinuousOn u (Icc a b))
    (hdu : ∀ t ∈ Ioc a b, HasDerivAt u (A t (u t)) t) :
    flowLinearMap hab A hA (u a) = u b := by
  exact solution_eqOn_interior A hA
    (solution_spec hab A hA (u a)).1.continuousOn hu
    (fun t ht => (solution_spec hab A hA (u a)).2.2 t ⟨ht.1.le, ht.2⟩)
    hdu (solution_spec hab A hA (u a)).2.1 ⟨hab, le_rfl⟩

#print axioms flow_apply_eq_of_solution_interior
#print axioms solution_norm_upper_interior
#print axioms solution_eqOn_halfline
end
end V10.PerronStableFlow
