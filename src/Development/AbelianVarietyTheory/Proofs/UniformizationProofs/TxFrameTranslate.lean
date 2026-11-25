module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaAverage
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_translate {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀) (hadd : g.IsAdd g₀ g') :
    g'.b = g.b ∧ ∀ χ z J, Good D.P.L z J → (val (g'.s χ) (𝟙 _) z J).val =
      cstH z (t (Multiplicative.ofAdd χ)).val * (val (g.s χ) (𝟙 _) z J).val := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  rw [ht.1, _root_.mul_one] at hb
  refine ⟨hb, fun χ z J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := hs χ z J hJ
  have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
  rw [e₀, _root_.mul_one] at e
  rw [e, Units.val_mul, ht.2 χ z J hJ, cst_eq, mul_comm]

theorem coef_translate {k : ℕ} {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀)
    (hadd : g.IsAdd g₀ g') {w : Frm D F k g.b} (hw : w.IsGen) {w' : Frm D F k g'.b} {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cstH z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g' w' χ = c * (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  obtain ⟨hb, hs⟩ := val_translate ht hadd
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hv z J hJ, hs χ z J hJ, e₁]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * cstH z (t (Multiplicative.ofAdd χ)).val * a

end Frames

attribute [local instance] gtGroup

end GlobalTheory.UT.ThetaAverage
end
