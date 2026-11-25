module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.VeryAmpleCharts

variable {Y : Scheme.{0}} {H : LB Y}

theorem isRetrocompact_nonzeroLocus (hH : H.IsLB) (s : LB.Sec H) :
    IsRetrocompact (X := Y) (nonzeroLocus s) := by
  intro V hV hVo
  have := isAffineHom_nonzeroLocus_ι hH s
  have h := (QuasiCompact.isCompact_preimage (f := (nonzeroLocus s).ι) V hVo hV).image
    (nonzeroLocus s).ι.continuous
  rwa [Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι] at h

theorem isAffineOpen_biInf_nonzeroLocus {κ : Type} (hH : H.IsLB) (s : κ → LB.Sec H)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (I : Finset κ) (hI : I.Nonempty) :
    IsAffineOpen (⨅ i ∈ I, nonzeroLocus (s i)) := by
  classical
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a => simpa using ha a
  | cons a t h _ ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert]
    exact isAffineOpen_nonzeroLocus_inf hH _ ih

theorem quasiSeparatedSpace_of_cover {κ : Type} (hH : H.IsLB) (s : κ → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    QuasiSeparatedSpace Y :=
  QuasiSeparatedSpace.of_isOpenCover (U := fun i => nonzeroLocus (s i)) hc
    (fun i => isRetrocompact_nonzeroLocus hH (s i)) fun i => (ha i).isQuasiSeparated

theorem compactSpace_of_finite_cover {κ : Type} [Finite κ] (D : κ → Y.Opens)
    (hc : ⨆ i, D i = ⊤) (ha : ∀ i, IsAffineOpen (D i)) : CompactSpace Y := by
  refine ⟨?_⟩
  have h := isCompact_iUnion fun i => (ha i).isCompact
  rwa [← TopologicalSpace.Opens.coe_iSup, hc] at h

theorem compact_quasiSeparated_isAffineOpen : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ ∀ I : Finset (Fin (m + 1)), I.Nonempty → IsAffineOpen (⨅ i ∈ I, nonzeroLocus (s i)) :=
  fun _ _ _ _ _ _ s hH hs =>
    ⟨compactSpace_of_finite_cover _ hs.1 fun i => (hs.2 i).1,
      quasiSeparatedSpace_of_cover hH s hs.1 fun i => (hs.2 i).1,
      isAffineOpen_biInf_nonzeroLocus hH s fun i => (hs.2 i).1⟩

end GlobalTheory.VeryAmpleCharts
