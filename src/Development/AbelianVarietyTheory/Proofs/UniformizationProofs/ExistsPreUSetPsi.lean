module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
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
noncomputable section
namespace GlobalTheory.UU
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def gtCoordSetPsi {e : ℕ} (g : GtCoord I D e G) (ψ) (h) : GtCoord I (setPsi D ψ h) e G where
  q := g.q
  q_hom := g.q_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  i := g.i
  i_hom := g.i_hom
  isKernel := g.isKernel
  t := g.t
  t_gen := g.t_gen
  t_mul := g.t_mul
  t_unit := g.t_unit
  t_weight := g.t_weight

def PreU.setPsi (U : PreU I D A G) (ψ) (h) : PreU I (setPsi D ψ h) A G where
  semi := U.semi
  gen := U.gen
  gen_hom := U.gen_hom
  P := U.P
  wA := U.wA
  wA_gen := U.wA_gen
  gt := fun e => gtCoordSetPsi (U.gt e) ψ h
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals := U.w_vals
  w_compat := U.w_compat
end

theorem exists_preU_setPsi : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) ψ h, ∃ (U' : PreU I (setPsi D ψ h) A G) (hP : U'.P = U.P), U'.gen = U.gen ∧ HEq U'.wA U.wA ∧ ∀ θ f, U.Theta θ f → ∃ θ', U'.Theta θ' f :=
  fun _ _ _ _ _ _ _ _ _ U ψ h => ⟨U.setPsi ψ h, rfl, rfl, HEq.rfl, fun θ _ hθ => ⟨θ, hθ⟩⟩
end GlobalTheory.UU
end
