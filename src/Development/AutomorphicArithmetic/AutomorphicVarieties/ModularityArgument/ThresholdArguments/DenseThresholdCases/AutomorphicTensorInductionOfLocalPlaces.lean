module

import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AutomorphicTensorInductionOfLocalPlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Fix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct

theorem UpperTheory.V.Hi.partUR2Type_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) :=
  fun _ _ _ _ _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY _ hT τ hτ =>
    UpperTheory.V.Hi.partUR2Type_of_typeProp s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY τ hτ
      fun W _ _ _ ρ hρ => (hT.2 W ρ τ hρ).1
end
