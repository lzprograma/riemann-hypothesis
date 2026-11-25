module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

namespace UpperTheory.V.Z.Win

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure LawsV (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop where
  dim : ∀ x, (rc x).lpDim = x.1
  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep →
    rc x = sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))
  det : ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) =
    sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j))
  prod : ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E)))
    (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) →
    rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ))
  supp : ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s →
    ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod
  sph : ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr
  sat : ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
    rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹)
  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)
  nu_eq : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s
  absCentral : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
  twist : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))
  central : ∀ (x : IrrGL (k := w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)
  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
    Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual
  inj : ∀ x y, Good y → rc x = rc y → x = y


variable (h) in
def IsRecV (rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), LawsV a ha ε rc

def ExtraV : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc → IsRecV h rc

end UpperTheory.V.Z.Win
