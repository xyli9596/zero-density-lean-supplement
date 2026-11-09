import V10.ProjectionRowFamily
import V10.ERealPlurisubharmonic

/-! Lemma 4.3 with literal finite holomorphic rows and Euclidean row norms. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace V10.ProjectionLemma43
open ProjectionRowFamily ProjectionAffineWindow HolomorphicProjectionAverage
set_option backward.isDefEq.respectTransparency false

/-- A global complete pluripolar set is exactly the negative-infinite locus
of one nontrivial, genuinely plurisubharmonic extended-real function. -/
def IsCompletePluripolar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Set E) : Prop :=
  ∃ Ψ : E → EReal, ERealPlurisubharmonic.Plurisubharmonic Ψ ∧
    (∃ c, Ψ c ≠ ⊥) ∧ S = {c | Ψ c = ⊥}

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [Nonempty Ω]

/-- Every input is a literal hypothesis on the finite original row or on
the prescribed real-affine windows. Projection nontriviality and equality
between the operator norm and Euclidean row norm are proved internally. -/
theorem finite_row_exceptional_potential {f : ι → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) univ) (hi : LinearIndependent ℂ f)
    (hn : ∀ z, ∃ j, f j z ≠ 0)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∃ (Ψ : EuclideanSpace ℂ ι → EReal) (κ : ℝ),
      ERealPlurisubharmonic.Plurisubharmonic Ψ ∧ 0 < κ ∧
      ExceptionalCone.LogHomogeneous Ψ κ ∧ (∃ c, Ψ c ≠ ⊥) ∧
      IsCompletePluripolar {c | Ψ c = ⊥} ∧
      (∀ c, ∀ α : ℂ, Ψ c = ⊥ → Ψ (α • c) = ⊥) ∧
      (∀ c, Ψ c ≠ ⊥ → ∀ dir : Ω, ∀ K : Set ℂ, IsCompact K →
        Tendsto (fun m => (Q m)⁻¹ * ∫ z in K,
          |Real.log (‖∑ j, f j (window (A dir m) (b dir m) z) * c j‖ /
            ‖rowVector f (window (A dir m) (b dir m) z)‖)|)
          atTop (𝓝 0)) := by
  have hF : Continuous (rowFunctional f) := rowFunctional_continuous
    (fun j => continuousOn_univ.mp (hf j).continuousOn)
  obtain ⟨Ψ, κ, hk, hhom, hgood, _, _, hcone, hlocal, hloss⟩ :=
    ProjectionExceptionalCone.actual_window_exceptional_potential hF
      (rowFunctional_ne_zero hn) (fun c _ => rowFunctional_analytic hf c)
      (fun _ hc => rowFunctional_nontrivial hi hc) A b hQ hQs
  have hpsh := ERealPlurisubharmonic.plurisubharmonic_of_ball_representations hlocal
  refine ⟨Ψ, κ, hpsh, hk, hhom, hgood, ⟨Ψ, hpsh, hgood, rfl⟩, hcone, ?_⟩
  intro c hc dir K hK
  simpa only [logProjection, rowFunctional_apply, rowFunctional_norm] using
    hloss c hc dir K hK

/-- The 69-page manuscript's Lemma 4.3, using genuine real two-dimensional
affine coordinates and Lebesgue area. Its conclusion is stronger than the
rectangle formulation: it holds on every compact subset of the parameter
plane. The single potential and pole cone work for all windows. -/
theorem lemma_4_3 {f : ι → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) univ) (hi : LinearIndependent ℂ f)
    (hn : ∀ z, ∃ j, f j z ≠ 0)
    (A : Ω → ℕ → (ℝ × ℝ) ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∃ (Ψ : EuclideanSpace ℂ ι → EReal) (κ : ℝ),
      ERealPlurisubharmonic.Plurisubharmonic Ψ ∧ 0 < κ ∧
      ExceptionalCone.LogHomogeneous Ψ κ ∧ (∃ c, Ψ c ≠ ⊥) ∧
      IsCompletePluripolar {c | Ψ c = ⊥} ∧
      (∀ c, ∀ α : ℂ, Ψ c = ⊥ → Ψ (α • c) = ⊥) ∧
      (∀ c, Ψ c ≠ ⊥ → ∀ dir : Ω, ∀ K : Set (ℝ × ℝ), IsCompact K →
        Tendsto (fun m => (Q m)⁻¹ * ∫ z in K,
          |Real.log (‖∑ j, f j (A dir m z + b dir m) * c j‖ /
            ‖rowVector f (A dir m z + b dir m)‖)|)
          atTop (𝓝 0)) := by
  let Ac : Ω → ℕ → ℂ ≃L[ℝ] ℂ := fun dir m =>
    Complex.equivRealProdCLM.trans (A dir m)
  obtain ⟨Ψ, κ, hpsh, hk, hhom, hgood, hpolar, hcone, hloss⟩ :=
    finite_row_exceptional_potential hf hi hn Ac b hQ hQs
  refine ⟨Ψ, κ, hpsh, hk, hhom, hgood, hpolar, hcone, ?_⟩
  intro c hc dir K hK
  have hK' : IsCompact (Complex.measurableEquivRealProd ⁻¹' K) :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr hK
  have h := hloss c hc dir _ hK'
  have he : ∀ m, (∫ z in Complex.measurableEquivRealProd ⁻¹' K,
      |Real.log (‖∑ j, f j (window (Ac dir m) (b dir m) z) * c j‖ /
        ‖rowVector f (window (Ac dir m) (b dir m) z)‖)|) =
      ∫ z in K, |Real.log (‖∑ j, f j (A dir m z + b dir m) * c j‖ /
        ‖rowVector f (A dir m z + b dir m)‖)| := by
    intro m
    exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun z => |Real.log (‖∑ j, f j (A dir m z + b dir m) * c j‖ /
        ‖rowVector f (A dir m z + b dir m)‖)|) K
  simpa only [he] using h

#print axioms finite_row_exceptional_potential
#print axioms lemma_4_3
end V10.ProjectionLemma43
