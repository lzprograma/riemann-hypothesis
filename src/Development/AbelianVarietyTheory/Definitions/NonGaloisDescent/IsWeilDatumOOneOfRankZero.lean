module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
import Mathlib.Algebra.Module.Torsion.Prod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RawLift

variable {D : D7}

def Lag (W : HSp D) : Type :=
  {Y : Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) //
    Module.finrank D.host.E Y = W.rank ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, star y.1 ⬝ᵥ W.gram.mulVec y'.1 = star y.2 ⬝ᵥ W.gram.mulVec y'.2}

def IsLagFrame (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Prop :=
  Submodule.span D.host.E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y.1

def ratMul {a b c : ℕ} (C : Matrix (Fin a) (Fin b) D.host.E) (u : Mx D b c) : Mx D a c :=
  HMul.hMul (C.map (incA D)) (u : Matrix (Fin b) (Fin c) (AE D))

def lagTerm {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) : ℂ :=
  ∫ u in 𝓕, f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) ∂μ

structure SWSetup (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V))
    (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  pos : V.IsPosDef
  big : 2 * W.rank < V.rank
  haarV : νV.IsHaarMeasure
  fdV : IsFundamentalDomain (GQ V) 𝓗 νV
  haarW : νW.IsHaarMeasure
  fdW : IsFundamentalDomain (GQ W) 𝓖 νW
  covol : IsCovolOne (ratL W V) μ 𝓕
  frame : ∀ Y, IsLagFrame W Y (fr Y)
  sigOK : V.SigOK

section Inhabitants

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
  {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}


theorem exists_lagFrame (W : HSp D) (Y : Lag W) : ∃ C, IsLagFrame W Y C := by
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  refine ⟨(fun a j => (b j).1.1 a, fun a j => (b j).1.2 a), ?_⟩
  have h := congrArg (Submodule.map Y.1.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
  exact h

def Lag.diag (W : HSp D) : Lag W :=
  ⟨LinearMap.range (LinearMap.prod LinearMap.id LinearMap.id), by
    rw [LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rfl⟩

instance (W : HSp D) : Inhabited (Lag W) := ⟨Lag.diag W⟩

theorem exists_haar_fundDomain (V : HSp D) :
    ∃ (ν : Measure (GA D V)) (𝓖 : Set (GA D V)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓖, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓖, inferInstance, h⟩

theorem exists_hecke_resEta (D : D7) (n : ℕ) : ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n := by
  obtain ⟨η, h1, -, h3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, h3.1, fun e he a => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]

end Inhabitants

end GlobalTheory.RawLift

end
