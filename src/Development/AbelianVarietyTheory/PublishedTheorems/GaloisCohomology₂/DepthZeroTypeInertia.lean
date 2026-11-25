module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace GlobalTheory.Published

def DepthZeroTypeInertia : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

end GlobalTheory.Published

end
