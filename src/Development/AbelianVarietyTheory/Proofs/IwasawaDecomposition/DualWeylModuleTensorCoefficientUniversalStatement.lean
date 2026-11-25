module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

open Formalism.L2.DIV GlobalTheory.CoefIrred in

theorem _root_.GlobalTheory.T.dualWeylModule_tensor_coefficient_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V]
      [Module ℂ V] (F : (∀ v, nablaSq ℂ n (lam v)) →ₘₗ[ℂ] V),
      ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V,
        ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hBasis : ∀ i, bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  let f := (bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))
  refine ⟨f, ?_, ?_⟩
  · have hComp : f.compMultilinearMap (tenMul lam) = F := by
      apply Module.Basis.ext_multilinear (fun τ => ssBasis ℂ (lam τ))
      intro i
      simp only [LinearMap.compMultilinearMap_apply, ← hBasis, f, Module.Basis.constr_basis]
    intro u
    exact congrArg (fun m => m u) hComp
  · intro g hg
    apply (bVV ℂ lam).ext
    intro i
    simp only [f, Module.Basis.constr_basis]
    rw [hBasis, hg]
