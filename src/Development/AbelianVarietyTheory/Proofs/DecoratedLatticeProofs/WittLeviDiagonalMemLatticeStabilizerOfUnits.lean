module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.LeviUnitK

variable {D : D7}

theorem mul_mem_of_sub_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) : (fun k => c * z k) ∈ latV S L P := by
  have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hc hz
  have e : (fun k => c * z k) = z + fun k => (c - 1) * z k := by
    funext k; simp only [Pi.add_apply]; ring
  rw [e]; exact add_mem hz h

theorem mem_iff_of_unit {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c c' : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    (hc' : finPart D (c' - 1) ∈ intAE D) (h1 : c' * c = 1) (z : Fin S.rank → AE D) :
    z ∈ latV S L P ↔ (fun k => c * z k) ∈ latV S L P := by
  refine ⟨mul_mem_of_sub_one hc, fun h => ?_⟩
  have h2 := mul_mem_of_sub_one hc' h
  have e : (fun k => c' * (c * z k)) = z := by funext k; rw [← mul_assoc, h1, one_mul]
  rwa [e] at h2

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (i : Fin n) (c a : AE D) :
    colMul x i (c * a) = fun k => c * colMul x i a k := by
  funext k; simp only [colMul, mul_assoc]

theorem diag_mulVec {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, i ≠ j → M i j = 0) (w : Fin n → R) (i : Fin n) : (M *ᵥ w) i = M i i * w i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj => by rw [h i j (Ne.symm hj), zero_mul]) (by simp)

theorem inv_offdiag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    ∀ i j, i ≠ j → (t⁻¹).1 i j = 0 := by
  intro i j hij
  have h1 : ((t⁻¹).1 * t.1) i j = 0 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne hij]
  have h2 : (t.1 * (t⁻¹).1) j j = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht k j hk, mul_zero]) (by simp)] at h1
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht j k (Ne.symm hk), zero_mul]) (by simp)] at h2
  calc (t⁻¹).1 i j = (t⁻¹).1 i j * (t.1 j j * (t⁻¹).1 j j) := by rw [h2, mul_one]
    _ = 0 := by rw [← mul_assoc, h1, zero_mul]

theorem inv_mul_diag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i : Fin n) :
    (t⁻¹).1 i i * t.1 i i = 1 := by
  have h1 : ((t⁻¹).1 * t.1) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [ht k i hk, mul_zero]) (by simp)] at h1

theorem adj_apply' {m n : ℕ} (x : Mx D m n) (i : Fin n) (j : Fin m) : GlobalTheory.MixModel.adj x i j = cA D (x j i) := rfl

theorem cA_sub_one {a : AE D} (h : finPart D (a - 1) ∈ intAE D) : finPart D (cA D a - 1) ∈ intAE D := by
  rw [← map_one (cA D), ← map_sub]
  exact (GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 h

end GlobalTheory.FinPl.LeviUnitK


open GlobalTheory.FinPl.LeviUnitK in
theorem GlobalTheory.FinPl.LeviUnitK.inK_levi : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  intro D S S₀ ρ d L L₀ v _hL hM t ht hg hu
  refine ⟨hg, fun y _ => ?_⟩
  have ht' := inv_offdiag t ht
  have hadj : ∀ i j, i ≠ j → GlobalTheory.MixModel.adj (t⁻¹).1 i j = 0 := fun i j hij => by
    rw [adj_apply', ht' j i (Ne.symm hij), map_zero]
  have eX : ∀ i, (d.pX *ᵥ (mt S (d.levi t) *ᵥ y)) i = t.1 i i * (d.pX *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pX_levi t, ← Matrix.mulVec_mulVec, diag_mulVec ht]
  have eY : ∀ i, (d.pY *ᵥ (mt S (d.levi t) *ᵥ y)) i = cA D ((t⁻¹).1 i i) * (d.pY *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pY_levi t, ← Matrix.mulVec_mulVec, diag_mulVec hadj, adj_apply']
  have e0 : d.p0 *ᵥ (mt S (d.levi t) *ᵥ y) = d.p0 *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi t]
  rw [hM y, hM (mt S (d.levi t) *ᵥ y), e0]
  simp only [eX, eY, colMul_mul]
  have hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => t.1 i i * colMul d.jX i ((d.pX *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (hu i).1.2 (hu i).2.2 (inv_mul_diag t ht i) _
  have hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => cA D ((t⁻¹).1 i i) * colMul d.jY i ((d.pY *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (cA_sub_one (hu i).2.2) (cA_sub_one (hu i).1.2)
      (by rw [← map_mul, mul_comm, inv_mul_diag t ht i, map_one]) _
  exact and_congr (forall_congr' hX) (and_congr (forall_congr' hY) Iff.rfl)

end
