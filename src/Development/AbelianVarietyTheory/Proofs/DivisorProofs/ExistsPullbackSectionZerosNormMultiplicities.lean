module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.Mix

theorem exists_secPull_props : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  intro k _ X Y p q σ π hπ M s
  refine ⟨GlobalTheory.Cartier.secPull s π, GlobalTheory.Cartier.nonzeroLocus_secPull s π, fun y =>
    Weight.nsq_pull_secPull M.φ π hπ s y, ?_⟩
  intro _ _ _ hη hs hs' w i hw
  have hc : w ∈ (M.B.pull π).U (fun _ => i) := by
    rw [GlobalTheory.Cartier.pull_U]; exact hw
  have hg : genericPoint Y ∈ (M.B.pull π).U (fun _ => i) := gen_mem hc
  have hg' : genericPoint Y ∈ π ⁻¹ᵁ M.B.U i := by
    have h := hg
    rw [GlobalTheory.Cartier.pull_U] at h
    exact h
  have h0 : genericPoint X ∈ M.B.U i := gen_mem hw
  have e : ((ratOfSec (L := (M.pull π hπ).B) (GlobalTheory.Cartier.secPull s π) hs' fun _ => i : Y.functionFieldˣ) :
      Y.functionField) = TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec h0, TrueGeo.SmallSec.fnMap_fnOf π hη h0 hg']
    exact (val_ratOfSec (L := M.B.pull π) (s := GlobalTheory.Cartier.secPull s π) (hs := hs') hg).trans
      (fnOf_resG (GlobalTheory.Cartier.pull_U M.B π fun _ => i).le hg _)
  exact ((presents_divOfRatSec _ _).isEqn (fun _ => i) w hc).mult_eq.trans (congrArg (Scheme.ord · w) e)

end GlobalTheory.Mix
