import V10.PerronStableTail
import V10.PerronStableTrajectory

/-! The actual bounded-solution initial subspace for a general asymptotically
constant system, in the original finite-dimensional space. -/
namespace V10.PerronStableSubspace
open Set Filter Module
open scoped Topology
noncomputable section
open V10.PerronDichotomyBasis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Actual boundedness is invariant under a fixed continuous linear coordinate
isomorphism. -/
theorem bounded_coordinates_iff (e : E ≃L[ℂ] F) {y : ℝ → E} {T : ℝ} :
    (∃ C : ℝ, ∀ t ≥ T, ‖e (y t)‖ ≤ C) ↔
      ∃ C : ℝ, ∀ t ≥ T, ‖y t‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖e.symm.toContinuousLinearMap‖ * C, fun t ht => ?_⟩
    calc
      ‖y t‖ = ‖e.symm (e (y t))‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (y t)‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖e.toContinuousLinearMap‖ * C, fun t ht => ?_⟩
    exact (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _))

lemma mem_map_equiv_symm (e : E ≃L[ℂ] F) (S : Submodule ℂ F) (x : E) :
    x ∈ S.map e.symm.toLinearEquiv.toLinearMap ↔ e x ∈ S := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    change e (e.symm v) ∈ S
    rw [e.apply_symm_apply]
    exact hv
  · intro hx
    refine ⟨e x, hx, ?_⟩
    exact e.symm_apply_apply x

variable [FiniteDimensional ℂ E]

/-- A genuine spectral cut below the unique top eigenvalue produces an actual
bounded-solution initial subspace of dimension n minus its algebraic
multiplicity. This classifies every actual shifted trajectory, not only the
constructed Volterra solutions. -/
theorem exists_tail_bounded_subspace {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {T₀ γ : ℝ} (μ : ℂ)
    (hA : ContinuousOn A (Ici T₀)) (hlim : Tendsto A atTop (𝓝 A₀))
    (hμ : Module.End.HasEigenvalue (A₀.toLinearMap : End ℂ E) μ) (hμre : γ < μ.re)
    (hrest : ∀ a : Module.End.Eigenvalues (A₀.toLinearMap : End ℂ E),
      a.val ≠ μ → a.val.re < γ) :
    ∃ T ≥ T₀, ∃ W : Submodule ℂ E,
      finrank ℂ W = finrank ℂ E - (A₀.toLinearMap : End ℂ E).charpoly.rootMultiplicity μ ∧
      ∀ y : ℝ → E, ContinuousOn y (Ici T) →
        (∀ t > T, HasDerivAt y
          ((A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E) (y t)) t) →
        (y T ∈ W ↔ ∃ C : ℝ, ∀ t ≥ T, ‖y t‖ ≤ C) := by
  obtain ⟨T, hT, δ, η, hδ, hη, ι, fι, dι, b, mode, lam, R,
    hgap, hRc, hRb, hsmall, hcount, hid⟩ :=
    exists_small_tail_coordinates μ hA hlim hμ hμre hrest
  let _ := fι
  let _ := dι
  let e := basisCoordinates b
  let S := boundedODEInitialStates T δ η hδ hη.le mode lam hgap R hRc hRb hsmall
  let W := S.map e.symm.toLinearEquiv.toLinearMap
  refine ⟨T, hT, W, ?_, ?_⟩
  · change finrank ℂ (S.map e.symm.toLinearEquiv.toLinearMap) = _
    rw [e.symm.toLinearEquiv.finrank_map_eq S]
    exact (finrank_boundedODEInitialStates T δ η hδ hη.le mode lam hgap R hRc hRb hsmall).trans hcount
  · intro y hy hyode
    have hzc : ContinuousOn (fun t => e (y t)) (Ici T) := e.continuous.comp_continuousOn hy
    have hzode : ∀ t > T, HasDerivAt (fun s => e (y s))
        (fun i => lam i * e (y t) i + R (clamp T t) (e (y t)) i) t := by
      intro t ht
      apply hasDerivAt_pi.mpr
      intro i
      have hh := (((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hyode t ht)
      change HasDerivAt (fun s => e (y s) i)
        (e ((A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E) (y t)) i) t at hh
      have hi := congrFun (hid ⟨t, ht.le⟩ (e (y t))) i
      change e ((A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E) (e.symm (e (y t)))) i = _ at hi
      rw [e.symm_apply_apply] at hi
      have hcl : clamp T t = ⟨t, ht.le⟩ := Subtype.ext (clamp_eq ht.le)
      rw [hcl, ← hi]
      exact hh
    change y T ∈ S.map e.symm.toLinearEquiv.toLinearMap ↔ _
    rw [mem_map_equiv_symm]
    exact (initial_mem_iff_bounded T δ η hδ hη.le mode lam hgap R hRc hRb hsmall hzc hzode).trans
      (bounded_coordinates_iff e)

#print axioms exists_tail_bounded_subspace
end
end V10.PerronStableSubspace
