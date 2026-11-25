module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)



namespace UpperTheory.V.Z.Ord

section At

variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {n : ℕ} (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

def ExpOf (π : CuspSub F n) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) : Prop :=
  ∃ a, IsLocalArtin h a ∧ ∃ (hh : Fin n → (F →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ),
    (∀ τ, StrictMono fun j => hh j τ) ∧ (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) ∧
    ∀ σ, π.IsLocComp w σ → IsSubquotient σ.ρ (PS ω)


omit [NumberField F] [_root_.NumberField.IsTotallyComplex F] [IsAlgClosure F Ω] in
def Unl (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) : Prop := ∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype


omit [IsAlgClosure F Ω] in
def TU (π : CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  Gam.TorAt π w ∧ ∀ s, Gam.SuppAt π w s → ImaginaryQuadraticEtaCharacter.Unl (Ideal.absNorm w.asIdeal) s

end At

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def ENDO : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      ∀ v : Vl l L, ExpOf ι (s.hw v) π (x.psi v)

end U

def OrdJac : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∀ (c : ℕ) (φ : (glIwa k n).T →* ℂˣ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (c + 1) → φ (eT k n i y) = 1) → ∀ v ∈ (glIwa k n).eig π c φ, v ≠ 0 →
    ∀ a : ℕ → ℂ, (∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp π (al k n (j + 1)) v = a (j + 1) • v) →
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsInvOn φ ω ∧ IsSubquotient π (PS ω) ∧
      ∀ j : Fin n, psEig ω (j + 1) = a (j + 1)

def ExpTor : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (n : ℕ), 1 ≤ n → ∀ (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A w),
    ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (π : CuspSub F n) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ), ExpOf ι h π ψ → Gam.TorAt π w ∧
      (Unl ψ → TU π w) ∧ ∀ t : ℝ, ImaginaryQuadraticEtaCharacter.WinAt π t w → ∀ i j (m : ℕ), 1 ≤ m →
        ψ i ^ m ≠ (ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m

def ConjTor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, GlobalTheory.ContraPair.DualIsConj π →
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
      TU π w → TU π w'

def ConjUnl : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (ρ : G E Ω →* GL (Fin n) (Qbar l)) (π : CuspSub E n), Continuous ρ → GlobalTheory.ContraPair.DualIsConj π →
    Af.AttC ι ρ π → ∀ w w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ ψ : Fin n → Dec (F := E) A →* (Qbar l)ˣ, W.HasFlag (ρ.comp (Dec (F := E) A).subtype) ψ →
        (Win.Unl1 ρ w' → Unl ψ) ∧
        ((∀ i j (m : ℕ), 1 ≤ m → ψ i ^ m ≠ (ψ j * (cycBar E Ω l).comp (Dec (F := E) A).subtype) ^ m) → Win.PotUnl ρ w')

def ExtChar : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (w : GroundTheory.Global.SemiLocal.PlacesOver L v) (A : ValuationSubring Ω) (h : IsPlaceOver A w.1),
    ((l : ℕ) : 𝓞 K) ∈ v.asIdeal → ∀ a, IsLocalArtin h a → ∀ (κ : Dec (F := K) A →* (Qbar l)ˣ) (ψ : Dec (F := L) A →* (Qbar l)ˣ),
    Continuous κ → (∀ (g : Dec (F := L) A) (g' : Dec (F := K) A), (g' : G K Ω) = AlgEquiv.restrictScalarsHom K (g : G L Ω) → ψ g = κ g') →
    ∀ ω hh, OrdChar ι a ω hh ψ → ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ω * χ.comp (Gam.nm w))

end UpperTheory.V.Z.Ord

end
