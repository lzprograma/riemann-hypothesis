module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' := pull_isLB hL F
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
