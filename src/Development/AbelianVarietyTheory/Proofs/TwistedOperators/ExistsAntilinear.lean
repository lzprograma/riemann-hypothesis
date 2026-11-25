module

import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR

namespace GlobalTheory.ConjEval

theorem exists_label {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    ∃ τ, labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
  first | exact _root_.GlobalTheory.ConjReading.lab_exists | exact @_root_.GlobalTheory.ConjReading.lab_exists | apply _root_.GlobalTheory.ConjReading.lab_exists <;> assumption

theorem conj_comp_eq_iff {E : Type} [Field E] (a b : E →+* ℂ) :
    (starRingEnd ℂ).comp a = b ↔ a = (starRingEnd ℂ).comp b := by
  constructor
  · rintro rfl
    ext x; simp
  · rintro rfl
    ext x; simp

theorem labE_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

theorem lab_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  _root_.GlobalTheory.ConjReading.lab_conj σ ρ

theorem evEx_conj {K C H H' Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] (σ : K →+* ℂ) (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev') (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (φ : C → Y → ℂ)
    (h : EvEx ((starRingEnd ℂ).comp σ) ev φ) : EvEx σ ev' fun f g => starRingEnd ℂ (φ f g) := by
  obtain ⟨j, hj⟩ := h
  choose x hx using hx
  refine ⟨⟨⟨fun f => x (j f), fun f f' => hinj (funext fun g => ?_)⟩, fun a f => hinj (funext fun g => ?_)⟩,
    fun f => funext fun g => ?_⟩
  · rw [ha', hx, hx, hx, map_add (f := _), ha, map_add (f := _)]
  · refine (hx _ g).trans ?_
    rw [j.map_smulₛₗ, hs, hs', hx, map_mul, RingHom.comp_apply, Complex.conj_conj]
  · exact (hx (j f) g).trans (congrArg (starRingEnd ℂ) (congrFun (hj f) g))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem levChi_principal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [h1]
  simp [LevCh.datWp, datY]

end GlobalTheory.ConjEval
