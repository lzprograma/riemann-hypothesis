module

public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top

variable {D : D7} {u : D.what₂.Word}

def HasMat (h : GA D D.sp.X')
    (y : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  h ∈ GfC D.sp.X' ∧ ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j = y.1 (finCongr (rankP D) i) (finCongr (rankP D) j)

def TopLev (K : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : K.lev.U, HasMat h κ.1) ∧ ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ)


open Classical in
structure IsJ (u : D.what₂.Word) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) : Prop where
  inj : Function.Injective j
  range : LinearMap.range j = ValC (gramC (gramP D) (embT D)) (sgT u)
  eqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
    ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
      j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y'


end GlobalTheory.Core.Rk.Top

end
