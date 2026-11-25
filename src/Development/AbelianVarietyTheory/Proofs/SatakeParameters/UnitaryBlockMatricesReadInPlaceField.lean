module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
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

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

theorem stdU_star_det_mul_det {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    star (M : Matrix (Fin n) (Fin n) D.host.E).det * (M : Matrix (Fin n) (Fin n) D.host.E).det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  have : (M : Matrix (Fin n) (Fin n) D.host.E).conjTranspose = star (M : Matrix (Fin n) (Fin n) D.host.E) := rfl
  rw [this, hU, Matrix.det_one]

theorem stdU_inv_eq_star {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
  have h1 : ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      = ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [← Matrix.mul_assoc, h1, hU]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem blkC_atR_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ {n : ℕ} (M : GL (Fin n) D.host.E), StdU D M → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (if IsOddPos s then ((((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose) else (atR D M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).map ι = ((M : Matrix (Fin n) (Fin n) D.host.E).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) ∧ Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det) = ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (if IsOddPos s then (-1 : ℤ) else 1) := by
  intro p _ X D pos Kc _ _ ι ρ hT n M hU v s
  have hT' := hT v s
  constructor
  · ext i j
    simp only [Matrix.map_apply]
    split_ifs with hs
    · have hinv : ((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) = atR D M⁻¹ (pos ⟨v, s⟩) := by
        simp [atR, map_inv]
      rw [Matrix.transpose_apply, hinv]
      simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [stdU_inv_eq_star D M hU, hT', ite_eq_left hs]
      simp [Matrix.star_apply]
    · simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [hT', ite_eq_right hs]
  · split_ifs with hs
    · have h := hT' (M : Matrix (Fin n) (Fin n) D.host.E).det
      rw [ite_eq_left hs] at h
      have h2 := hT' (star (M : Matrix (Fin n) (Fin n) D.host.E).det)
      rw [ite_eq_left hs, star_star] at h2
      rw [← h2, zpow_neg_one]
      have h3 := congrArg (fun x => ι (embT D (pos ⟨v, s⟩) x)) (stdU_star_det_mul_det D M hU)
      simp only [map_mul, map_one] at h3
      exact (eq_inv_of_mul_eq_one_left h3)
    · rw [hT', ite_eq_right hs, zpow_one]

end GlobalTheory.TwV.DelA
