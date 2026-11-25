module

import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  first | exact _root_.GlobalTheory.TwU.Model.intAtA_add | exact @_root_.GlobalTheory.TwU.Model.intAtA_add | apply _root_.GlobalTheory.TwU.Model.intAtA_add <;> assumption

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := GlobalTheory.TwU.Model.intAtA_mul ha hb

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  GlobalTheory.TwU.Model.intAtA_int x

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  exact GlobalTheory.TwU.Model.intAtA_sum s f h

theorem intAtA_one_apply (a b : Fin N) :
    IntAtA (F := F) P ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  rw [Matrix.one_apply]
  split_ifs
  · simpa using intAtA_int (F := F) (P := P) 1
  · simpa using intAtA_int (F := F) (P := P) 0

theorem qpow_facts (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    iA F E (((qOf P : ℕ) : E) ^ n) * iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ = 1 ∧
      IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ n)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  refine ⟨by rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one], ?_⟩
  have := intAtA_int (F := F) (P := P) (((qOf P : ℕ) : 𝓞 E) ^ n)
  simpa using this

theorem intAtA_of_congAt (n : ℕ) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (a b : Fin N) :
    IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  obtain ⟨hdc, hd⟩ := qpow_facts (F := F) P n
  have e : (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b =
      (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b +
        iA F E (((qOf P : ℕ) : E) ^ n) * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ *
          ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, hdc, one_mul, Matrix.sub_apply]; ring
  rw [e]
  exact intAtA_add (intAtA_one_apply a b) (intAtA_mul hd (h a b))

theorem congAt_mul (n : ℕ) {k k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (h' : CongAt P n k') :
    CongAt P n (k * k') := by
  intro a b
  have hk' := intAtA_of_congAt n h'
  set K := (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set K' := (k' : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have e : ((k * k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      (K - 1) * K' + (K' - 1) := by
    rw [Units.val_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  refine intAtA_add (intAtA_sum _ _ fun j _ => ?_) (h' a b)
  rw [← mul_assoc]
  exact intAtA_mul (h a j) (hk' j b)

theorem congAt_conj (n : ℕ) {A B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hA : CongAt P n A)
    (hB : ∀ r s, IntAtA (F := F) P ((B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s))
    (hBi : ∀ r s, IntAtA (F := F) P (((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s)) :
    CongAt P n (B⁻¹ * A * B) := by
  intro a b
  set Bm := (B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Bi := ((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Am := (A : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hBB : Bi * Bm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : ((B⁻¹ * A * B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      Bi * ((Am - 1) * Bm) := by
    rw [Units.val_mul, Units.val_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← hBB, Matrix.mul_assoc]
  rw [e, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_sum _ _ fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine intAtA_sum _ _ fun l _ => ?_
  have e2 : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Bi a j * ((Am - 1) j l * Bm l b)) =
      Bi a j * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Am - 1) j l) * Bm l b := by ring
  rw [e2]
  exact intAtA_mul (intAtA_mul (hBi a j) (hA j l)) (hB l b)

end GlobalTheory.CongMove

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

theorem nearAt_conj_ratA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (κ x k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (f g : GL (Fin N) E)
    (hk : ∀ r s, IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hki : ∀ r s, IntAtA (F := F) P (((k⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hm : ∀ r s, IntAtA (F := F) P (((k⁻¹ * x * k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hmi : ∀ r s, IntAtA (F := F) P ((((k⁻¹ * x * k)⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hκ : GlobalTheory.TwU.CongAt P n (κ⁻¹ * x)) (hg : GlobalTheory.TwU.NearAt P n (k⁻¹ * x * k) g)
    (he : GlobalTheory.TwU.CongAt P n (k⁻¹ * GlobalTheory.TwU.ratA F f)) (hei : GlobalTheory.TwU.CongAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * k)) :
    GlobalTheory.TwU.NearAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * κ * GlobalTheory.TwU.ratA F f) g := by
  unfold NearAt at hg ⊢
  set Fr := ratA F f
  set G := ratA F g
  set m := k⁻¹ * x * k
  have key : (Fr⁻¹ * κ * Fr)⁻¹ * G =
      (Fr⁻¹ * k) * (k⁻¹ * (κ⁻¹ * x) * k) * (m⁻¹ * (k⁻¹ * Fr) * m) * (m⁻¹ * G) := by
    simp only [m]
    group
  rw [key]
  refine congAt_mul n (congAt_mul n (congAt_mul n hei ?_) ?_) hg
  · have h := congAt_conj n hκ (B := k) hk hki
    simpa only [inv_inv] using h
  · have h := congAt_conj n he (B := m) hm hmi
    exact h

end GlobalTheory.CongMove
