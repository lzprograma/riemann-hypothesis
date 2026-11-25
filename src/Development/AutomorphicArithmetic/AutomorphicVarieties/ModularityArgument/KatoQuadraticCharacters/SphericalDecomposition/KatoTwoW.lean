module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
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

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

def KatoTwoW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Used l Ω K e N θ ψ W →
    ∀ (ι : Qbar l ≃+* ℂ) (f : Af.Newform (2 * e + 1)), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → WitAQ ι W →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ))

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

theorem kUse' (hK : KatoTwoW) (_ : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ)
    (h : (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.1.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf h.2

end UpperTheory.V.Z.Kato.WeilSphericalRecords
