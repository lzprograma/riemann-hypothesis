module

import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
import Mathlib.Analysis.CStarAlgebra.Classes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_int_eq_prod_of_galois_permuted_integral :
    ∀ (T : Type) [Fintype T] (f : T → ℂ), (∀ t, IsIntegral ℤ (f t)) → (∀ σ : ℂ ≃+* ℂ, ∃ u : T ≃ T, ∀ t, f (u t) = σ (f t)) → ∃ n : ℤ, (n : ℂ) = ∏ t, f t := by
  apply UpperTheory.V.CongNum.exists_int_prod
