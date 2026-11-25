module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.FlatRow

theorem isOpen_closure_of_isOpen_components {Z : Type} [TopologicalSpace Z]
    (h : ∀ z : Z, IsOpen (irreducibleComponent z)) {W : Set Z} (hW : IsOpen W) : IsOpen (closure W) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨irreducibleComponent z, ?_, h z, mem_irreducibleComponent⟩
  have hne : (irreducibleComponent z ∩ W).Nonempty := mem_closure_iff.1 hz _ (h z) mem_irreducibleComponent
  intro y hy
  refine mem_closure_iff.2 fun O hO hyO => ?_
  obtain ⟨a, -, ha⟩ := isIrreducible_irreducibleComponent.isPreirreducible O W hO hW ⟨y, hy, hyO⟩ hne
  exact ⟨a, ha⟩

theorem isOpen_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens), IsClosed (U : Set (Xo.XF c)) → IsOpen (FramedFlatCoordinates.compactification Y U) := by
  intro E _ _ _ H Dw l Xo c Y U _
  have i₀ : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have i₁ : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hn : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := fun x => by
    let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (FramedFlatCoordinates.genFibre Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (RingHom.id c.F)))
  have := Y.jQ_open
  exact isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)

end GlobalTheory.FlatRow
