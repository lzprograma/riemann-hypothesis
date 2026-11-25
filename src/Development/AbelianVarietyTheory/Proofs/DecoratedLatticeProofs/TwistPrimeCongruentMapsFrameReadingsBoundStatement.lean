module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
open Formalism.L2.Ker

theorem _root_.GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  exact @GlobalTheory.Transport.TwistRead.qread
