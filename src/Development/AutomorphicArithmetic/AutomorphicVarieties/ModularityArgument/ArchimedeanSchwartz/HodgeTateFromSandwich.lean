module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJStandardLFourier
public import GroundTheory.AutomorphicForms.SmoothRepContragredient
public import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical


namespace UpperTheory.V.Z.Inf

def LocDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V), π.IsIrreducible → IsAdmissible π →
    ∀ (ξ : V) (ℓ : Module.Dual ℂ V), ℓ ∈ smoothVectors (Representation.dual π) →
    ∀ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ →
    ∃ (N D : ℂ → ℂ) (c : ℝ), IsExp N ∧ IsExp D ∧ D ≠ 0 ∧ ∀ s : ℂ, s.re < -c →
      zetaIntegral (localHaar n v) Φ (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) π ξ ℓ g⁻¹) (1 - s) * D s = N s

def LocUnr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V), π.IsIrreducible → IsAdmissible π →
    fixedVectors π (integralGL (v.adicCompletion K) n) ≠ ⊥ → ∀ z : Fin n → ℂˣ,
    Spherical.IsSatakeParameter (F := v.adicCompletion K) π (localHaar n v) z → ∀ t : ℂ,
      LFunction (F := v.adicCompletion K) π t = ∏ i, (1 - (z i : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t))⁻¹ ∧
      LFunction (F := v.adicCompletion K) (contragredient π) t =
        ∏ i, (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t))⁻¹

def SatDict : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (σ : CuspSub K n)
    (h : Cm.carrier σ ≤ centralCuspForms K n) (D : AdelicDecomposition (Cm.toRep σ h).toModule)
    (v : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk σ).HasSat v B →
    ∃ z : Fin n → ℂˣ, Spherical.IsSatakeParameter (F := v.adicCompletion K) (D.finite.π v) (localHaar n v) z ∧
      B = Finset.univ.val.map z

def CoefSm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (μ : Measure (Reduction.normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (σ : CuspSub K n), Cm.carrier σ ≤ centralCuspForms K n → ∀ φ₂ : cuspForms K n,
    ∃ T : σ.V →ₗ[ℂ] Sm K n, (∀ φ : σ.V, (T φ).1 = GJGlobal.matrixCoeff μ φ.1.1 φ₂.1) ∧
      ∀ (τ : K →+* ℂ) (u : ℂ) (φ φ' : σ.V), φ'.1 = cap τ u φ.1 → T φ' = cap τ u (T φ)

def ArchShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (ψ : Sm K n) (m : (K →+* ℂ) → Multiset ℂ),
    (∀ τ u, cap τ u ψ = ((m τ).map (u + ·)).prod • ψ) → ∀ fi : AdelicGLn.InfiniteAdelicGL K n → ℂ,
    (∀ x, fi x = ψ.1 ((AdelicGLn.prodEquiv K n).symm (x, 1))) → (∃ x, fi x ≠ 0) →
    ∀ (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure],
    ∃ (φ φ' : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ)) (k k' : ℂ), k ≠ 0 ∧ k' ≠ 0 ∧
      Differentiable ℂ (archZeta μ φ fi) ∧ archZeta μ φ fi ≠ 0 ∧
      (∀ s, archZeta μ φ' fi (s + 1) = k * (linPoly (∑ τ, m τ)).eval s * archZeta μ φ fi s) ∧
      ∀ (g : AdelicGLn.InfiniteAdelicGL K n → ℂ) (s : ℂ),
        archZeta μ (archMatrixFourier φ') g s = k' * archZeta μ (archMatrixFourier φ) g (s + 1)

def ArchBridge : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (μ : Measure (AdelicGLn.InfiniteAdelicGL K n))
    [μ.IsHaarMeasure], (∀ x, ∃ y, archComp K n (infGL K n y) = x) ∧
    (∀ y, (AdelicGLn.prodEquiv K n).symm (archComp K n (infGL K n y), 1) = infGL K n y) ∧
    (∀ y, archAbsDet (archComp K n (infGL K n y)) = nrm (toL y.val)) ∧
    ∃ (e : ℝ) (c c' : ℂ), e ≠ 0 ∧ c ≠ 0 ∧ c' ≠ 0 ∧ ∀ Φ : Lie K n → ℂ, IsTest Φ →
      ∃ φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ),
        (∀ (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ) (f : Lie K n → ℂ), ContinuousOn f (invSet K n) →
          (∀ y, fi (archComp K n (infGL K n y)) = f (toL y.val)) → ∀ s : ℂ,
            archZeta μ φ fi s = c * ∫ x, Φ x * f x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n)) ∧
        ∀ y, archSchwartz (archMatrixFourier φ) (archComp K n (infGL K n y)).val = c' * four e Φ (toL y.val)

def BridgeOf : Prop := HaarL → ArchBridge
def ArchOf : Prop := ShiftL → FourD → TestEx → ArchBridge → ArchShift

end UpperTheory.V.Z.Inf
