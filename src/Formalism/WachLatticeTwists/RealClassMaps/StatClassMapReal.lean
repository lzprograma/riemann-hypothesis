module

public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatBKInIso
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement

@[expose] public section

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

section Defs
variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']

def gRow (D : LatData O Γ VT VT') {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁]
    [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] D.T')
    (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = D.ρTl' g (v (π t))) :
    H1 ρ₁ →ₗ[O] H1 D.ρTl' :=
  mapH1 ρ₁ D.ρTl' (v.toLinearMap ∘ₗ π) hc he

end Defs

end Formalism.RepresentationBoundsCohomology.FIN
