module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩


end GlobalTheory.SeeSaw.LocPlInhab
end
