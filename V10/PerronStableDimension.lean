import V10.PerronStableSubspaceGraph
import V10.PerronStableFlowConverse

/-!
# The actual bounded-ODE initial subspace and its dimension

The graph is constructed from the unique mixed Volterra fixed points. Here
both calculus directions identify it with precisely the initial values of
actual bounded continuous solutions of the diagonal-plus-perturbation ODE.
Thus its dimension is a conclusion for an actual ODE solution space, not an
assumption about a prescribed linear solution map or an abstract graph.
-/

noncomputable section
open Set Module
open scoped BoundedContinuousFunction
namespace V10.PerronStableSubspace
open V10.PerronStableFlowODE

variable {ι : Type*} [Fintype ι]
variable (T δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
variable (mode : ι → Bool) (lam : ι → ℂ)
variable (hgap : ∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re)
variable (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
variable (hsmallR : ∀ s, ‖R s‖ ≤ η) (hsmall : decayMass δ * η < 1)

/-- The genuine differential equation on the open part of the half-line. -/
def IsBoundedODESolution (u : Ici T →ᵇ (ι → ℂ)) : Prop :=
  ∀ r > T, HasDerivAt (extend u)
    (fun i => lam i * extend u r i + R (clamp T r) (extend u r) i) r

include hδ hgap in
omit [Fintype ι] in
lemma unstable_re_pos (i : ι) (hi : mode i = false) : 0 < (lam i).re := by
  have hg := hgap i
  simp only [hi, Bool.false_eq_true, ↓reduceIte] at hg
  exact hδ.trans_le hg

/-- Every constructed fixed point is a real bounded continuous ODE solution. -/
theorem fixedPoint_isBoundedODESolution (v : ι → ℂ) :
    IsBoundedODESolution T lam R
      (fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v) := by
  let u := fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall v
  intro r hr
  apply fixed_point_hasDerivAt mode lam v R hR hsmallR u
    (fun i hi => unstable_re_pos δ hδ mode lam hgap i hi) ?_ hr
  intro t i
  have he := congrArg (fun w : Ici T →ᵇ (ι → ℂ) => w t i)
    (fixedPoint_spec T δ η hδ hη mode lam hgap R hR hsmallR hsmall v)
  change u t i = forcingVector T mode lam v t i + integralVector T mode lam R u t i at he
  simpa only [forcingVector, integralVector, Complex.ofReal_sub] using he

/-- Every actual bounded solution is the unique mixed fixed point with its
own stable initial coordinates. -/
theorem boundedODESolution_eq_fixedPoint (u : Ici T →ᵇ (ι → ℂ))
    (hu : IsBoundedODESolution T lam R u) :
    u = fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall
      (liftStable mode (fun i : {i : ι // mode i = true} => u ⟨T, by exact le_refl T⟩ i.val)) := by
  apply fixedPoint_unique T δ η hδ hη mode lam hgap R hR hsmallR hsmall
  ext t i
  have he := bounded_ode_formula mode lam R hR hsmallR u
    (fun i hi => unstable_re_pos δ hδ mode lam hgap i hi) hu t i
  change u t i = forcingVector T mode lam
    (liftStable mode (fun j : {i : ι // mode i = true} => u ⟨T, by exact le_refl T⟩ j.val)) t i +
      integralVector T mode lam R u t i
  cases hi : mode i <;>
    simpa only [forcingVector, integralVector, liftStable, LinearMap.coe_mk,
      AddHom.coe_mk, hi, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      Complex.ofReal_sub] using he

/-- Membership is characterized by the actual ODE and boundedness in BCF. -/
theorem mem_initialGraph_iff_boundedODESolution (y : ι → ℂ) :
    y ∈ initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall ↔
      ∃ u : Ici T →ᵇ (ι → ℂ), u ⟨T, by exact le_refl T⟩ = y ∧ IsBoundedODESolution T lam R u := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall
      (liftStable mode v), ?_, ?_⟩
    · exact hv
    · exact fixedPoint_isBoundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _
  · rintro ⟨u, hy, hu⟩
    refine ⟨(fun i : {i : ι // mode i = true} => u ⟨T, by exact le_refl T⟩ i.val), ?_⟩
    change fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall
      (liftStable mode (fun i : {i : ι // mode i = true} => u ⟨T, by exact le_refl T⟩ i.val))
        ⟨T, by exact le_refl T⟩ = y
    rw [← boundedODESolution_eq_fixedPoint T δ η hδ hη mode lam hgap R hR hsmallR hsmall u hu]
    exact hy

/-- The submodule is defined by actual bounded ODE initial values. Its closure
under linear operations follows from the proved graph characterization. -/
def boundedODEInitialStates : Submodule ℂ (ι → ℂ) where
  carrier := {y | ∃ u : Ici T →ᵇ (ι → ℂ),
    u ⟨T, by exact le_refl T⟩ = y ∧ IsBoundedODESolution T lam R u}
  zero_mem' := (mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall 0).mp
    (initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall).zero_mem
  add_mem' := by
    intro x y hx hy
    apply (mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _).mp
    exact (initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall).add_mem
      ((mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _).mpr hx)
      ((mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _).mpr hy)
  smul_mem' := by
    intro c x hx
    apply (mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _).mp
    exact (initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall).smul_mem c
      ((mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall _).mpr hx)

theorem boundedODEInitialStates_eq_initialGraph :
    boundedODEInitialStates T δ η hδ hη mode lam hgap R hR hsmallR hsmall =
      initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall := by
  ext y
  exact (mem_initialGraph_iff_boundedODESolution T δ η hδ hη mode lam hgap R hR hsmallR hsmall y).symm

/-- Exact dimension of the actual bounded-ODE initial-state subspace. -/
theorem finrank_boundedODEInitialStates :
    finrank ℂ (boundedODEInitialStates T δ η hδ hη mode lam hgap R hR hsmallR hsmall) =
      Fintype.card {i : ι // mode i = true} := by
  rw [boundedODEInitialStates_eq_initialGraph]
  exact finrank_initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall

#print axioms fixedPoint_isBoundedODESolution
#print axioms boundedODESolution_eq_fixedPoint
#print axioms mem_initialGraph_iff_boundedODESolution
#print axioms finrank_boundedODEInitialStates
end V10.PerronStableSubspace
