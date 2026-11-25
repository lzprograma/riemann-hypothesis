module

import Lemmata.CharpolySmul
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.cpSmul :
    ∀ {n : ℕ} {R : Type} [CommRing R] (a : R) (M : Matrix (Fin n) (Fin n) R), (a • M).charpoly = M.charpoly.scaleRoots a ∧
          ∀ x : Fin n → R, (∏ i, (X - C (x i))).scaleRoots a = ∏ i, (X - C (a * x i)) := by
  intro n R _ a M
  refine ⟨Matrix.charpoly_smul M a, fun x ↦ ?_⟩
  simpa only [← Matrix.diagonal_smul, Matrix.charpoly_diagonal, Pi.smul_apply, smul_eq_mul]
    using (Matrix.charpoly_smul (Matrix.diagonal x) a).symm