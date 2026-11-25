module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.LetterMap

def coeffMap {K L : Type} [Field K] [Field L] (f : K →+* L) : LaurentSeries K →+* LaurentSeries L where
  toFun g := HahnSeries.map g f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
theorem _root_.GlobalTheory.LetterMap.coeffMap_ofPowerSeries {K L : Type} [Field K] [Field L] (f : K →+* L)
    (g : PowerSeries K) :
    _root_.GlobalTheory.LetterMap.coeffMap f (HahnSeries.ofPowerSeries ℤ K g) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.map f g) := by
  ext n
  change f ((HahnSeries.ofPowerSeries ℤ K g).coeff n) = _
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.LetterMap.det_ne_zero (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K₁ : Type) [Field K₁] :
    _root_.Formalism.L2.Pj.arcDet Dw K₁ ≠ 0 := by
  unfold _root_.Formalism.L2.Pj.arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : (Matrix.of fun i k ↦
      (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (Sigma.mk τ)).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp
  rw [h, ← AlgHom.map_det]
  intro h0
  rw [map_eq_zero_iff _ (MvPolynomial.rename_injective _ sigma_mk_injective)] at h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ h0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.LetterMap.num_algebraMap {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {K₁ : Type} [Field K₁]
    (P : MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) :
    _root_.Formalism.L2.Pj.QAt.arcNum (algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P) = P := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁)) := by
    unfold _root_.Formalism.L2.Pj.ArcS
    exact IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (_root_.GlobalTheory.LetterMap.det_ne_zero Dw K₁))
  have hex : ∃ Q, algebraMap (MvPolynomial (_root_.Formalism.L2.Pj.ArcLt Dw) (LaurentSeries K₁)) (_root_.Formalism.L2.Pj.ArcS Dw K₁) Q =
      algebraMap _ (_root_.Formalism.L2.Pj.ArcS Dw K₁) P := ⟨P, rfl⟩
  unfold _root_.Formalism.L2.Pj.QAt.arcNum
  rw [dite_eq_left hex]
  exact hinj hex.choose_spec

end GlobalTheory.LetterMap
