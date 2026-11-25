module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecBGenerates
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_thetaFrame : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, NuGe D Q F v 1 θ 0 ∧ ∃ (σ : D.toPre.SecB 1 0) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1) σF (D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB D.toPre F).left 1 ∧ (∀ j, (θ.s 0).f j = σF.f j) ∧ ¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j := by
  intro hL _ _ _ V _ _ _ ϖ hϖ D Q hQ F _ _ v hv
  obtain ⟨b, hb⟩ := IndivisibleSection.exists_secBGenerates hL.secBaseChange V (maximalIdeal V) D
  obtain ⟨Φ, f, hf, hf0, -, -⟩ := integralFamily_of_strictMin hL V ϖ hϖ D Q hQ 1 le_rfl 0 b (fun z hz => by
    have h := QForm.Q_pos hϖ (D := D) hQ hz
    rw [QForm.Q_zero hϖ (D := D) hQ, zero_add, one_smul]
    omega)
  obtain ⟨θ, hθ⟩ := FamBaseChange.main hL.globalFns V (maximalIdeal V) D 1 Φ f hf F
  refine ⟨θ, (integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ f hθ).1, b, θ.s 0, hf0 ▸ hθ 0, fun _ => rfl, ?_⟩
  rintro ⟨σ', hσ'⟩
  have h1 : SecIsMul D.toPre.P.A.hom ϖ b σ' := hσ'
  obtain ⟨a, ha, -⟩ := hb σ'
  have h2 : SecIsMul D.toPre.P.A.hom (ϖ * a) b b := fun j => by
    refine (h1 j).trans ?_
    rw [ha j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  have h3 : SecIsMul D.toPre.P.A.hom 1 b b := fun j => by
    simp only [scal, resTop, map_one, _root_.one_mul]
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one a ((hb b).unique h2 h3))

end GlobalTheory
