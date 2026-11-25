module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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

@[expose] public section

noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix


variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def bP (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m - 1)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
    Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g

def bM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) : GL (Fin (B.R.N B.R.m)) B.fields.E :=
  Classical.epsilon fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g

def coP (u : B.Word) (a : I.ι) (w : B.places.Pl) :
    ((I.perIn u a).S'.Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ]
      ((I.perIn u a).S'.Cl → MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m - 1) × Fin (B.R.N B.R.m - 1)) ℂ) :=
  LinearMap.pi fun c =>
    actP (I.perIn u a).sgT (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bP I u a w c)⁻¹)) ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ
      LinearMap.proj c

def coM (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    (Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) →ₗ[ℂ]
      MvPolynomial (B.fields.Tau × Fin (B.R.N B.R.m) × Fin (B.R.N B.R.m)) ℂ :=
  actP (lamT (B.hcW u) B.R.m) (invTrK (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (bM I u a w c)⁻¹)) ∘ₗ
    polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m)) ∘ₗ
    (((I.chIn u a).S B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)).toLinearMap

end GlobalTheory.PerQ.Co

end
