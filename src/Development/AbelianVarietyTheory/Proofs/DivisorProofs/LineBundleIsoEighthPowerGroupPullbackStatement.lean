module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.lineBundleIso_eighthPower_groupPullback : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  first | exact @GlobalTheory.Poinc.Eq8.lbIso_eighth_pull
