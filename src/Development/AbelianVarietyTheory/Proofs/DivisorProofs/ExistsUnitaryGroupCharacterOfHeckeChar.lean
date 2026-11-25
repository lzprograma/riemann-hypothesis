module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology

namespace GlobalTheory.SplitDetCharacter

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 :=
  GlobalTheory.SplitDetCharF.mul_det_sub_one a M h

theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) :=
  GlobalTheory.SplitDetCharF.cut_eq a1 a2 hd

theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 :=
  GlobalTheory.SplitDetCharF.cut_mul e2 a1 a2 hd e3

variable {D : D7}

theorem det_mul_conj (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det = 1 :=
  GlobalTheory.SplitDetCharF.det_mul_conj
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero⟩ g

theorem algebraMap_norm (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) = z * cA D z :=
  GlobalTheory.SplitDetCharF.algebraMap_norm
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩ z

theorem char_norm {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (x x' : (AE D)ˣ)
    (hx : (x' : AE D) = cA D x) : χ x * χ x' = 1 :=
  GlobalTheory.SplitDetCharF.char_norm
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩ h x x' hx

theorem char_eq_of_mul_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (y x : (AE D)ˣ)
    (hy : (y : AE D) * cA D x = 1) : χ y = χ x :=
  GlobalTheory.SplitDetCharF.char_eq_of_mul_conj
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩ h y x hy

def cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : GA D V →* (AE D)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin V.rank) (R := AE D)).comp (matHom V))

theorem cutDet_val (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V) :
    (cutDet ε h V g : AE D) = (1 - ε) + ε * (Formalism.L2.Theta.mt V g).det := rfl

theorem cutDet_eq_one (ε : AE D) (h : ε * ε = ε) (V : HSp D) (g : GA D V)
    (hg : ∀ i j, ε * (Formalism.L2.Theta.mt V g - 1) i j = 0) : cutDet ε h V g = 1 :=
  GlobalTheory.SplitDetCharF.cutDet_eq_one ε h g hg

theorem continuous_cutDet (ε : AE D) (h : ε * ε = ε) (V : HSp D) : Continuous (cutDet ε h V) :=
  GlobalTheory.SplitDetCharF.continuous_cutDet ε h

theorem cutDet_real (ε : AE D) (h1 : ε * ε = ε) (h3 : infPart D ε = 0) (V : HSp D) (g : GA D V) (hg : g ∈ GinfC V) :
    cutDet ε h1 V g = 1 :=
  GlobalTheory.SplitDetCharF.cutDet_real ε h1 h3 g hg

theorem det_supp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) * ((Formalism.L2.Theta.mt V g).det - 1) = 0 :=
  GlobalTheory.SplitDetCharF.det_supp hg

theorem cutDet_same (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (a1 : ε * e = e) (a2 : ε * cA D e = 0) {V : HSp D} {g : GA D V}
    {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) : cutDet ε h1 V g = x :=
  GlobalTheory.SplitDetCharF.cutDet_same ε h1 a1 a2 hg hx

theorem cutDet_conj (ε : AE D) (h1 : ε * ε = ε) {e : AE D} (he : e * e = e) (a1 : ε * e = 0) (a2 : ε * cA D e = cA D e)
    {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hg : SuppAt e V g) (hx : IsDetAt e V g x) :
    (cutDet ε h1 V g : AE D) * cA D x = 1 :=
  GlobalTheory.SplitDetCharF.cutDet_conj
    ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), (GlobalTheory.LatVac.gram_det_isUnit V).ne_zero⟩
    ε h1 he a1 a2 hg hx



theorem exists_character : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  rintro D ε ⟨h1, -, h3, h4, h5⟩ V χ n hχ hres
  refine ⟨χ.comp (cutDet ε h1 V), hχ.1.comp (continuous_cutDet ε h1 V), fun g hg => ?_, fun v η hv g hg => ?_,
    fun e he g x hg hx => ?_⟩
  · rw [MonoidHom.comp_apply, cutDet_real ε h1 h3 V g hg, map_one]
  · rw [MonoidHom.comp_apply, cutDet_eq_one ε h1 V g fun i j => ?_, map_one]
    rw [← hg i j, ← mul_assoc, mul_comm ε, h5 v η hv, zero_mul]
  · rw [MonoidHom.comp_apply]
    rcases h4 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [cutDet_same ε h1 a1 a2 hg hx]
    · exact char_eq_of_mul_conj hres _ x (cutDet_conj ε h1 he.1 a1 a2 hg hx)

end GlobalTheory.SplitDetCharacter
