module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace UpperTheory.V.Lev

def SsCmp {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x y : WD h) : Prop :=
  AbW x ∨ AbW y → ∀ s, x.charPol s = y.charPol s

theorem SsCmp.of_eq {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} {x y : WD h} (e : x = y) : SsCmp x y := fun _ _ => by rw [e]

def SsCalc : Prop :=
  ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v),
    (∀ (n : ℕ) (x : WD h) (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) → AbW x) ∧
    (∀ x x' y y' : WD h, SsCmp x y → SsCmp x' y' → SsCmp (x.lpSum x') (y.lpSum y')) ∧
    ∀ x y z : WD h, z.lpDim = 1 → (SsCmp (x.lpChar z) (y.lpChar z) ↔ SsCmp x y)

def SsMove : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (x y : WD h) (x' y' : WD h'),
      WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → SsCmp x' y' → SsCmp x y

abbrev WO {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := IsWDOf ι r y

end UpperTheory.V.Lev

end
