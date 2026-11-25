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

namespace GlobalTheory.KerDia

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre}

def ent (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β}
    (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') :
    (Fr B.fields.emb B.embLL (B.R.N i) → ℂ) →ₗ[ℂ] (Fr B.fields.emb B.embLL (B.R.N (i + 1)) → ℂ) :=
  (I.rho u a i b p * I.rho' u a i b' p') • (((I.chain l u a).divDe i).comp
    ((fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ∘ₗ jetMap (jetC I.J.cD (I.th u a i b b' p p')) 0 ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))).comp ((I.chain l u a).sharp i)))

theorem Kmap_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.chain l u a).Kmap i c c' = ent I l u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := rfl

end GlobalTheory.KerDia
