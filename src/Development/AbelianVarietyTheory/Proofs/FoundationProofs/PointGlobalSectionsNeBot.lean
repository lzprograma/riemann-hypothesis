module

public import Formalism.LocalRingCardinality.DataDIV
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}


open Classical in
def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  H0 _ _ := ⊤
  Cl _ := Set Unit
  supp _ _ := ∅
  inter _ _ := 1
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
