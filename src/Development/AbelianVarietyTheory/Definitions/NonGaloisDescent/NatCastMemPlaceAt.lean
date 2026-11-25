module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

noncomputable section

namespace GlobalTheory.GeoTie

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts

section Field

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (φ : F →+* ℂ_[p])

theorem norm_int_le_one (a : 𝓞 F) : ‖φ (a : F)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (φ (a : F)) := by
    convert map_isIntegral_int φ a.isIntegral_coe
    exact Subsingleton.elim _ _
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (φ (a : F)) := hx.tower_top
  have h3 : ‖φ (a : F)‖₊ ≤ 1 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  exact_mod_cast h3

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']
  exact Padic.norm_p_lt_one

def placeAt [NumberField F] : HeightOneSpectrum (𝓞 F) where
  asIdeal :=
    { carrier := {a | ‖φ (a : F)‖ < 1}
      add_mem' := fun {a b} ha hb => by
        have e : ((a + b : 𝓞 F) : F) = (a : F) + (b : F) := by simp
        simp only [Set.mem_ofPred_eq, e, map_add (f := _)] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have e : ((c * a : 𝓞 F) : F) = (c : F) * (a : F) := by simp
        simp only [Set.mem_ofPred_eq, smul_eq_mul, e, map_mul, norm_mul] at *
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one φ c)).trans_lt ha }
  isPrime :=
    { ne_top' := fun h => by
        have h1 := (Ideal.eq_top_iff_one _).1 h
        change ‖φ ((1 : 𝓞 F) : F)‖ < 1 at h1
        simp at h1
      mem_or_mem' := fun {a b} h => by
        change ‖φ ((a * b : 𝓞 F) : F)‖ < 1 at h
        change ‖φ (a : F)‖ < 1 ∨ ‖φ (b : F)‖ < 1
        have e : ((a * b : 𝓞 F) : F) = (a : F) * (b : F) := by simp
        rw [e, map_mul, norm_mul] at h
        by_contra hn
        rw [not_or, not_lt, not_lt] at hn
        exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2)) }
  ne_bot := fun h => by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := by
      rw [← h]
      change ‖φ (((p : ℕ) : 𝓞 F) : F)‖ < 1
      have e : (((p : ℕ) : 𝓞 F) : F) = (p : F) := by simp
      rw [e, map_natCast]
      exact norm_p_lt_one
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 h1))

theorem mem_placeAt [NumberField F] (a : 𝓞 F) : a ∈ (placeAt φ).asIdeal ↔ ‖φ (a : F)‖ < 1 := Iff.rfl

theorem natCast_mem_placeAt [NumberField F] : ((p : ℕ) : 𝓞 F) ∈ (placeAt φ).asIdeal := by
  have e : (((p : ℕ) : 𝓞 F) : F) = (p : F) := by simp
  rw [mem_placeAt, e, map_natCast]
  exact norm_p_lt_one

def kurC : Subfield ℂ_[p] := (φ.fieldRange ⊔ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p).topologicalClosure

def PAt (_φ : F →+* ℂ_[p]) : Type := ℂ_[p]

instance : Field (PAt φ) := inferInstanceAs (Field ℂ_[p])
instance : IsAlgClosed (PAt φ) := inferInstanceAs (IsAlgClosed ℂ_[p])
instance : Algebra F (PAt φ) := φ.toAlgebra

def toCp : PAt φ →+* ℂ_[p] := RingHom.id ℂ_[p]

theorem toCp_algebraMap (a : F) : toCp φ (algebraMap F (PAt φ) a) = φ a := rfl

structure IsReading (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]) : Prop where
  comp : ∀ a, k (io a) = φ a
  int : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x


variable {φ} in
def IsReading.alg {T : CDVR} {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (h : IsReading φ T io k) :
    letI := io.toAlgebra; T.Fr →ₐ[F] PAt φ :=
  letI := io.toAlgebra
  { (show T.Fr →+* PAt φ from k) with commutes' := h.comp }

end Field

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p])


variable {Xo c φ} in
def IsReadPt {T : CDVR} {io : c.F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (h : IsReading φ T io k) (y : IntFr Xo c T io)
    (u : Ix Dw → (PAt φ)ˣ) (z : FrPt Xo c (PAt φ)) : Prop :=
  letI := io.toAlgebra
  ∃ w : FrPt Xo c (PAt φ), FrMap h.alg y.1 w ∧ FrBor u w z


variable {Xo c φ} in
def IsIntPt (z : FrPt Xo c (PAt φ)) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (k : T.Fr →+* ℂ_[p]) (h : IsReading φ T io k) (y : IntFr Xo c T io)
    (u : Ix Dw → (PAt φ)ˣ), y.IsAlg ∧ (∀ a, ‖toCp φ (u a)‖ = 1) ∧ IsReadPt h y u z

def PtC : Type := {z : FrPt Xo c (PAt φ) // IsIntPt z}

variable {Xo c φ}

def valC (z : FrPt Xo c (PAt φ)) (f : Rul Xo c) : ℂ_[p] := toCp φ (evR Xo c f z)

theorem valC_add (z : FrPt Xo c (PAt φ)) (f g : Rul Xo c) : valC z (f + g) = valC z f + valC z g :=
  evalAt_add _ _ f g z

theorem valC_smul (z : FrPt Xo c (PAt φ)) (a : c.F) (f : Rul Xo c) : valC z (a • f) = φ a * valC z f :=
  evalAt_smul _ _ a f z

theorem valC_zero (z : FrPt Xo c (PAt φ)) : valC z 0 = 0 := evalAt_zero _ _ z

abbrev HkKer (𝔓 : Ideal (𝓞 E)) (q i : ℕ) (z : FrPt Xo c (PAt φ)) : Type := hkKer (Xo := Xo) 𝔓 q i (PAt φ) z

def IsHkQuot (𝔓 : Ideal (𝓞 E)) (q i : ℕ) (z : FrPt Xo c (PAt φ)) (C : HkKer 𝔓 q i z) (z' : FrPt Xo c (PAt φ)) : Prop :=
  hkRelFr 𝔓 q i (GlobalTheory.ThetaTrace.hkTr Xo c q) (PAt φ) z C z'

end Points

end GlobalTheory.GeoTie

end
