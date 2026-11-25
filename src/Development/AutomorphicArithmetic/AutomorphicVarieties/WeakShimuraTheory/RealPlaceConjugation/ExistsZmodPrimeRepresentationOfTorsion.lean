module

public import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.Module.ZMod
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem UpperTheory.V.Ws.exists_zmod_representation (n : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] (ρ : Representation R Γ M) :
    ∃ ρ' : Representation (ZMod n) Γ M, ∀ g m, ρ' g m = ρ g m := by
  refine ⟨{ toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap n
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext m
    simp
  · intro g h
    ext m
    simp
  · intro g m
    rfl

theorem UpperTheory.V.Ws.exists_zmod_prime_representation_of_torsion :
    ∀ (l : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ m : M, l • m = 0) → ∀ ρ : Representation R Γ M, ∃ (_ : Module (ZMod (l ^ 1)) M) (ρ' : Representation (ZMod (l ^ 1)) Γ M), ∀ g m, ρ' g m = ρ g m := by
  intro l Γ _ R M _ _ _ hl ρ
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule (fun m => by simpa using hl m)
  obtain ⟨ρ', hρ'⟩ := UpperTheory.V.Ws.exists_zmod_representation (l ^ 1) Γ R M ρ
  exact ⟨this, ρ', hρ'⟩
