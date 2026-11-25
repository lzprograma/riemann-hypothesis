module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := levG _ (R.βW i) (R.datWp i R.triv)

def jointVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)

def IsUnitVec (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1

def VecNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 ∧
    ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0

def TrivAt (V : HSp D) (f : AE D) (g : GA D V) : Prop := ∀ a b, f * (mt V g - 1) a b = 0

def IsFinIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) : Prop :=
  ∃ ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε

def latIndex (W : HSp D) (g : GA D W) : ℕ :=
  ((Formalism.L2.NTheta.LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).relIndex (Formalism.L2.NTheta.LamHat W)

def LevProd (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  levW R i ≤ GfC (Wc D i) ∧ (∀ k ∈ levW R i, levChi _ (R.βW i) (R.datWp i R.triv) k = 1) ∧
  ∃ cmp : HeightOneSpectrum (𝓞 D.host.F) → (GA D (Wc D i) →* GA D (Wc D i)),
    (∀ v f, IsFinIdem D v f → ∀ g, SuppF (Wc D i) f (cmp v g) ∧ TrivAt (Wc D i) f (g * (cmp v g)⁻¹)) ∧
    (∀ g ∈ GfC (Wc D i), (g ∈ levW R i ↔ ∀ v, cmp v g ∈ levW R i) ∧ {v | cmp v g ∉ levW R i}.Finite)

end GlobalTheory.RawLift

end
