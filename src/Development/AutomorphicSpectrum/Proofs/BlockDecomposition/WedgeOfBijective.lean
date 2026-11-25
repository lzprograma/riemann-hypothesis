module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

end GlobalTheory.CompanionTheory.Hodge.WedgeField
