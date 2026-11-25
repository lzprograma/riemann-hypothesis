module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LocLanglands.SatakeLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero (h := h) = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

end GlobalTheory.LocLanglands.SatakeLaw

namespace GlobalTheory.LocLanglands.SatakeLaw

theorem sat_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ),
    HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro h1 h2 h3 h4 h5 h6 E Ω _ _ _ _ _ A w h a ha e rc H x α hα
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified h1 h2 h3 h4 h5 h6 (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.LocLanglands.SatakeLaw
