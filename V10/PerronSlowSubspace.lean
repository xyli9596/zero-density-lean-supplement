import V10.PerronSlowRates
import V10.PerronStableFlowUniqueness
import V10.PerronStableSpace
import V10.PerronStableFlowGlobal

/-! The spectral-rate endgame for the slow-growth subspace. -/
noncomputable section
open Set Filter Module
open scoped Topology
namespace V10.PerronSlowSubspace

section Spectrum
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Finiteness of the actual spectrum produces a strict cut below a unique
leading eigenvalue. The cut is constructed, not an additional hypothesis. -/
theorem exists_leading_cut (A : End ℂ V) (μ : ℂ)
    (hmax : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < μ.re) :
    ∃ γ : ℝ, γ < μ.re ∧ ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ := by
  classical
  let s : Finset A.Eigenvalues := Finset.univ.filter (fun a => a.val ≠ μ)
  by_cases hs : s.Nonempty
  · let a := s.sup' hs (fun a => a.val.re)
    have ha : a < μ.re := (Finset.sup'_lt_iff hs).mpr fun a ha =>
      hmax a (Finset.mem_filter.mp ha).2
    refine ⟨(a + μ.re) / 2, by linarith, ?_⟩
    intro b hb
    have hbs : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    have hh : b.val.re ≤ a := Finset.le_sup' (f := fun a => a.val.re) hbs
    linarith
  · refine ⟨μ.re - 1, by linarith, ?_⟩
    intro a ha
    exact (hs ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩).elim

omit [FiniteDimensional ℂ V] in
/-- For a cut below the sole leading eigenvalue, being below the leading
rate and being below the cut are the same on the actual finite spectrum. -/
theorem eigenvalue_below_cut_iff (A : End ℂ V) {μ : ℂ} {γ : ℝ}
    (hγ : γ < μ.re)
    (hrest : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ)
    (a : A.Eigenvalues) : a.val.re < γ ↔ a.val.re < μ.re := by
  constructor
  · exact fun h => h.trans hγ
  · intro h
    apply hrest a
    intro he
    simp [he] at h

omit [FiniteDimensional ℂ V] in
theorem eigenvalue_eq_leading_of_not_below_cut (A : End ℂ V) {μ : ℂ} {γ : ℝ}
    (hrest : ∀ a : A.Eigenvalues, a.val ≠ μ → a.val.re < γ)
    (a : A.Eigenvalues) (ha : ¬a.val.re < γ) : a.val = μ := by
  by_contra h
  exact ha (hrest a h)

end Spectrum

section InteriorODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The actual invertible finite-time flow propagates nonvanishing without
requiring a two-sided derivative at the initial boundary. -/
theorem solution_ne_zero_interior {A : ℝ → E →L[ℂ] E} {x : ℝ → E} {T : ℝ}
    (hA : ContinuousOn A (Ici T)) (hxcont : ContinuousOn x (Ici T))
    (hode : ∀ t > T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    ∀ t ≥ T, x t ≠ 0 := by
  intro t ht hn
  have hc := hA.mono (show Icc T t ⊆ Ici T from Icc_subset_Ici_self)
  have heq := PerronStableFlow.flow_apply_eq_of_solution_interior ht A hc
    (hxcont.mono Icc_subset_Ici_self) (fun s hs => hode s hs.1)
  have hz : PerronStableFlow.flowLinearMap ht A hc (x T) = 0 := heq.trans hn
  exact hx ((PerronStableFlow.flow_eq_zero_iff ht A hc (x T)).mp hz)

/-- A nontrivial solution on a closed half-line has a nonzero initial value. -/
theorem initial_ne_zero_of_nontrivial {A : ℝ → E →L[ℂ] E} {x : ℝ → E} {T : ℝ}
    (hA : ContinuousOn A (Ici T)) (hxcont : ContinuousOn x (Ici T))
    (hode : ∀ t > T, HasDerivAt x (A t (x t)) t)
    (hx : ∃ t ≥ T, x t ≠ 0) : x T ≠ 0 := by
  intro hzero
  obtain ⟨t, ht, hn⟩ := hx
  have heq := PerronStableFlow.flow_apply_eq_of_solution_interior ht A
    (hA.mono Icc_subset_Ici_self) (hxcont.mono Icc_subset_Ici_self)
    (fun s hs => hode s hs.1)
  rw [hzero, map_zero] at heq
  exact hn heq.symm

/-- The real Perron theorem in exactly the regularity class of a solution
on a closed half-line: continuity at the initial point and interior ODE. -/
theorem perron_growth_exponent_interior {A : ℝ → E →L[ℂ] E}
    {A₀ : E →L[ℂ] E} {x : ℝ → E} {T : ℝ}
    (hA : ContinuousOn A (Ici T)) (hlim : Tendsto A atTop (𝓝 A₀))
    (hxcont : ContinuousOn x (Ici T))
    (hode : ∀ t > T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 μ.val.re) := by
  apply PerronGeneral.perron_growth_exponent (T := T + 1)
    (hA.mono (Ici_subset_Ici.mpr (by linarith))) hlim
  · intro t ht
    exact hode t (by linarith)
  · exact solution_ne_zero_interior hA hxcont hode hx _ (by linarith)

/-- Lemma 3.6: the actual slow initial values form a complex subspace with
codimension equal to the algebraic multiplicity of the unique leading
eigenvalue. Every nonzero solution has its actual logarithmic rate, and all
solutions outside the constructed subspace have the leading rate.

Only continuity at the initial boundary and the interior differential
equation are required. The paper's additional `m < n` assumption is not
needed for this stronger result (it merely makes the slow dimension positive).
-/
theorem lemma_3_6 {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {T₀ : ℝ}
    (hA : ContinuousOn A (Ici T₀)) (hlim : Tendsto A atTop (𝓝 A₀))
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (A₀.toLinearMap : End ℂ E) μ)
    (hmax : ∀ a : Module.End.Eigenvalues (A₀.toLinearMap : End ℂ E),
      a.val ≠ μ → a.val.re < μ.re) :
    ∃ V : Submodule ℂ E,
      finrank ℂ V = finrank ℂ E - (A₀.toLinearMap : End ℂ E).charpoly.rootMultiplicity μ ∧
      ∀ x : ℝ → E, ContinuousOn x (Ici T₀) →
        (∀ t > T₀, HasDerivAt x (A t (x t)) t) →
        (∃ t ≥ T₀, x t ≠ 0) →
        ∃ ℓ : ℝ, Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ) ∧
          (x T₀ ∈ V ↔ ℓ < μ.re) ∧ (x T₀ ∉ V → ℓ = μ.re) := by
  classical
  obtain ⟨γ, hγ, hrest⟩ := exists_leading_cut (A₀.toLinearMap : End ℂ E) μ hmax
  have hcut : ∀ a : Module.End.Eigenvalues (A₀.toLinearMap : End ℂ E), a.val.re ≠ γ := by
    intro a
    by_cases ha : a.val = μ
    · simpa [ha] using hγ.ne'
    · exact (hrest a ha).ne
  obtain ⟨T, hT, W, hdim, hW⟩ := PerronStableSubspace.exists_tail_bounded_subspace
    μ hA hlim hμ hγ hrest
  have hAseg : ContinuousOn A (Icc T₀ T) := hA.mono Icc_subset_Ici_self
  let V : Submodule ℂ E := W.map (PerronStableFlow.flowLinearEquiv hT A hAseg).symm.toLinearMap
  refine ⟨V, ?_, ?_⟩
  · exact (PerronStableFlow.flow_pullback_finrank hT A hAseg W).trans hdim
  · intro x hxc hode hnontriv
    have hx := initial_ne_zero_of_nontrivial hA hxc hode hnontriv
    obtain ⟨a, ha⟩ := perron_growth_exponent_interior hA hlim hxc hode hx
    have hne : ∀ᶠ t in atTop, x t ≠ 0 := by
      filter_upwards [eventually_ge_atTop T₀] with t ht
      exact solution_ne_zero_interior hA hxc hode hx t ht
    have hxtail : ContinuousOn x (Ici T) := hxc.mono (Ici_subset_Ici.mpr hT)
    have hweighted := hW (PerronSlowRates.weighted γ x)
      (PerronSlowRates.weighted_continuousOn γ hxtail)
      (fun t ht => PerronSlowRates.weighted_hasDerivAt (hode t (hT.trans_lt ht)))
    have hweightmem : PerronSlowRates.weighted γ x T ∈ W ↔ x T ∈ W :=
      W.smul_mem_iff (Complex.exp_ne_zero _)
    have hmem : x T₀ ∈ V ↔ x T ∈ W := by
      rw [PerronStableFlow.mem_flow_pullback_iff hT A hAseg W]
      rw [PerronStableFlow.flow_apply_eq_of_solution_interior hT A hAseg
        (hxc.mono Icc_subset_Ici_self) (fun t ht => hode t ht.1)]
    have hmemcut : x T₀ ∈ V ↔ a.val.re < γ :=
      hmem.trans (hweightmem.symm.trans (hweighted.trans
        (PerronSlowRates.weighted_bounded_iff_rate_lt hxtail ha hne (hcut a))))
    refine ⟨a.val.re, ha, hmemcut.trans
      (eigenvalue_below_cut_iff (A₀.toLinearMap : End ℂ E) hγ hrest a), ?_⟩
    intro hnot
    have he := eigenvalue_eq_leading_of_not_below_cut (A₀.toLinearMap : End ℂ E)
      hrest a (fun h => hnot (hmemcut.mpr h))
    exact congrArg Complex.re he

/-- The literal set of initial values of actual slow solutions, together with
zero. Existence of an actual solution and its actual logarithmic limit are
part of the membership statement. -/
def slowInitialValues (A : ℝ → E →L[ℂ] E) (T σ : ℝ) : Set E :=
  {v | v = 0 ∨ ∃ x : ℝ → E, x T = v ∧ ContinuousOn x (Ici T) ∧
    (∀ t > T, HasDerivAt x (A t (x t)) t) ∧
    ∃ ℓ : ℝ, ℓ < σ ∧ Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ)}

/-- The constructed space equals the literal slow-initial-value set. The
forward implication constructs an actual global solution for every initial
value, so the space characterization cannot be vacuous. -/
theorem lemma_3_6_initial_values {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {T : ℝ}
    (hA : ContinuousOn A (Ici T)) (hlim : Tendsto A atTop (𝓝 A₀))
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (A₀.toLinearMap : End ℂ E) μ)
    (hmax : ∀ a : Module.End.Eigenvalues (A₀.toLinearMap : End ℂ E),
      a.val ≠ μ → a.val.re < μ.re) :
    ∃ V : Submodule ℂ E,
      finrank ℂ V = finrank ℂ E - (A₀.toLinearMap : End ℂ E).charpoly.rootMultiplicity μ ∧
      (V : Set E) = slowInitialValues A T μ.re := by
  obtain ⟨V, hdim, hclass⟩ := lemma_3_6 hA hlim μ hμ hmax
  refine ⟨V, hdim, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    obtain ⟨x, hxt, hxc, hode⟩ := PerronStableFlow.exists_solution_halfline A hA v
    have hx : ∃ t ≥ T, x t ≠ 0 := ⟨T, le_rfl, by rwa [hxt]⟩
    obtain ⟨ℓ, hℓ, hmem, _⟩ := hclass x hxc hode hx
    exact Or.inr ⟨x, hxt, hxc, hode, ℓ, hmem.mp (by rwa [hxt]), hℓ⟩
  · rintro (rfl | ⟨x, hxt, hxc, hode, ℓ, hℓlt, hℓ⟩)
    · exact V.zero_mem
    by_cases hv0 : v = 0
    · simp [hv0]
    have hx : ∃ t ≥ T, x t ≠ 0 := ⟨T, le_rfl, by rwa [hxt]⟩
    obtain ⟨ℓ', hℓ', hmem, _⟩ := hclass x hxc hode hx
    have heq : ℓ' = ℓ := tendsto_nhds_unique hℓ' hℓ
    have hv' := hmem.mpr (heq ▸ hℓlt)
    rwa [hxt] at hv'

end InteriorODE

#print axioms perron_growth_exponent_interior
#print axioms lemma_3_6
#print axioms lemma_3_6_initial_values
end V10.PerronSlowSubspace
