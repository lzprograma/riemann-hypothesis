module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU

namespace GlobalTheory

theorem pullB_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T₀ : Over (Spec (CommRingCat.of R))) (φ : TF (R := R) F ⟶ T₀) (k : ℕ) (f : ∀ α, SecBT D T₀ k α) (s : Raw D F k), PullB D F φ k f s → ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TF (R := R) F) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (s α) (lift ρ x).left z J = sval (f α) (lift (ρ ≫ φ) x).left z J := by
  intro R _ _ D F _ _ T₀ φ k f s h α T ρ x z J hJ
  have e : (lift ρ x).left ≫ (φ ▷ D.P.A).left = (lift (ρ ≫ φ) x).left := by
    rw [← Over.comp_left, lift_whiskerRight]
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) (lift ρ x).left z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left (lift ρ x).left z J hJ).2.1 (f α)
  have hJ' : Good D.P.L ((lift ρ x).left z) (fun ψ => J ((lift ρ x).left ≫ ψ)) := fun ψ => hJ _
  rw [e] at b
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

end GlobalTheory
