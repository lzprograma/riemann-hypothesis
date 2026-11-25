module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDimStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem surjective_of_isFinite_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  intro K _ A B f hdim hfin
  obtain ⟨hBi, -, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B
  set g := f.hom.left
  have eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))
  have eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))
  have dA := GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A
  have dB := GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B
  rw [eA] at dA
  rw [eB] at dB

  have hm : StrictMono (g : A.X.left → B.X.left) := by
    intro a b hab
    have h1 : g a ≤ g b := (show b ⤳ a from hab.1).map g.continuous
    refine lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_
    have e : g b = g a := ((show g b ⤳ g a from h1).antisymm h2).eq
    have hd := (g.isDiscrete_preimage_singleton (g a)).to_subtype
    have : (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1
    have hba : b = a := congrArg Subtype.val this.eq
    rw [hba]
  refine ⟨?_⟩
  by_contra hns
  have hη : genericPoint B.X.left ∉ Set.range g := by
    intro hη
    apply hns
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    intro y
    exact (genericPoint_specializes y).mem_closed hc hη
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 dA.ge
  have hlast : (l.map g hm).last < genericPoint B.X.left := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_
    have e := ((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq
    rw [e, LTSeries.last_map]
    exact ⟨_, rfl⟩
  have := Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)
  rw [dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim] at this
  norm_cast at this
  omega

end GlobalTheory.AV.AbVar
