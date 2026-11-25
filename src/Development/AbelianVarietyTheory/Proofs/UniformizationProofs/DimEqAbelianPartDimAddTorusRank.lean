module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory.UU

theorem HidaSetting.smoothDim_model : AllSet fun {_} _ _ _ {A} {G} _ _ _ => SmoothOfRelativeDimension A.g G.hom := by
  intro V _ _ _ A G _ _ s
  have hs : Smooth G.hom := s.semi.smooth
  have : GeometricallyConnected G.hom := s.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have a := A.smoothDim
  have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
    have : IsIso s.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.hom))
    rw [← Over.w s.gen.hom]; infer_instance
  have c : SmoothOfRelativeDimension n ((Over.pullback (jK V)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hn
  have h₁ : n = A.g :=
    (H1.dim_unique _ c b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  exact h₁ ▸ hn

theorem Tower.dim_eq_add_finrank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  intro V _ _ _ A G _ _ s t g'
  have hG : SmoothOfRelativeDimension A.g G.hom := HidaSetting.smoothDim_model V A G s
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  have h₀ : SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X := fun h =>
    TQ.dim_eq_add_finrank _ s.X _ (t.l 0).Q A.g g'
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG) h
  refine ⟨h₀, fun a ha => h₀ ?_⟩
  obtain ⟨h, -⟩ := a.b_pb 0
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 ha

end GlobalTheory.UU
