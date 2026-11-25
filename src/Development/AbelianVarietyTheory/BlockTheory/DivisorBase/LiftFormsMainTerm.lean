module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

variable {D : D7}



def absPow (half : Bool) (P : Pl D.host.E) (k : D.host.E) : ℂ :=
  cond half ((Real.sqrt (NumberField.FinitePlace.mk P k) : ℝ) : ℂ) 1

def conjRes (s : ℂ →+* ℂ) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map s.toMonoidHom).comp (χ PP)



variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



set_option genInjectivity false in
set_option genSizeOfSpec false in
structure LiftInput (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BV : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  coef : CoefA (Vc D i)

  io : LowT (R.MW i σ) →ₗ[ℂ] coef.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  ν : Measure (GA D (Vc D i))

  fd : Set (GA D (Vc D i))

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem lab_base (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_base ρ)⟩
  unfold lab
  rw [dite_eq_left h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [labE_base] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem isONBasis_onb {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (p : ℕ)
    (h : ∀ a, M.ε τ a = decide ((a : ℕ) < p)) : IsONBasis (gramAt D V τ) (cart M τ) (onb M τ) p := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hJ : (Matrix.diagonal fun a => (((if M.ε τ a = true then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    split_ifs <;> simp
  refine ⟨fun a => if M.ε τ a = true then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : (a : ℕ) < p
    · left; simp [h a, ha]
    · right; simp [h a, ha, Nat.le_of_not_lt ha]
  · rw [hJ, ← M.fr_gram τ, onb]
    have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · rw [hJ, cart, onb, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

end
