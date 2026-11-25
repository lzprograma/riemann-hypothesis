module

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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

variable {D : D7}

def IsDefiniteSpace (V : HSp D) : Prop := V.SigOK ∧ V.IsDefinite

def IsOpenCompactLevel (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧ IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

def levelFin (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (Lev.toAfE V K).comap (finHom V).range.subtype

def classGroupAt (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : Bridge.Gf V) : Subgroup (GQ V) :=
  Bridge.stab (Bridge.ratF V) (levelFin V K) x

structure IsClassFun (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (Φ : GA D V → ℂ) : Prop where

  left : ∀ γ ∈ GQ V, ∀ h, Φ (γ * h) = Φ h

  real : ∀ k ∈ GinfC V, ∀ h, Φ (h * k) = Φ h

  level : ∀ k ∈ Lev.levA V K, ∀ h, Φ (h * k) = Φ h

def ClassSumIntegral : Prop :=
  ∀ (D : D7) (V : HSp D), IsDefiniteSpace V →
    ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K →
      ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 →
        ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levelFin V K) y →
          ∀ (z : I → GA D V), (∀ i, (finHom V).rangeRestrict (z i) = y i) →
            ∀ (Φ : GA D V → ℂ), IsClassFun V K Φ →
              (∀ i, Finite (classGroupAt V K (y i))) ∧ IntegrableOn Φ 𝓕 μ ∧
                ∫ h in 𝓕, Φ h ∂μ = ∑ i, ((Nat.card (classGroupAt V K (y i)) : ℂ))⁻¹ * Φ (z i)

variable {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}

theorem map_conj_inv {G H : Type} [Group G] [Group H] (f : G →* H) (a b : G) : f (a⁻¹ * b * a) = (f a)⁻¹ * f b * f a := by
  rw [map_mul, map_mul, map_inv]

theorem mem_levelFin (w : GA D V) : (finHom V).rangeRestrict w ∈ levelFin V K ↔ Lev.finE V w ∈ K := Iff.rfl

theorem mem_classGroupAt (z : GA D V) (γ : GQ V) :
    γ ∈ classGroupAt V K ((finHom V).rangeRestrict z) ↔ Lev.finE V (z⁻¹ * (γ : GA D V) * z) ∈ K := by
  unfold classGroupAt
  rw [Bridge.mem_stab]
  have e : ((finHom V).rangeRestrict z)⁻¹ * Bridge.ratF V γ * (finHom V).rangeRestrict z =
      (finHom V).rangeRestrict (z⁻¹ * (γ : GA D V) * z) := by
    have e0 : Bridge.ratF V γ = (finHom V).rangeRestrict (γ : GA D V) := by
      simp only [Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e0]
    exact (map_conj_inv (finHom V).rangeRestrict z γ).symm
  rw [e]
  exact mem_levelFin _

end GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral

end
