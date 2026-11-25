module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

variable {D : D7}

def compFin (D : D7) (w : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F w ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)).toRingHom

def ExtUnramAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime], P.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D.host.F) P

def CharUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → (∀ w, w ≠ v → compFin D w (finPart D (x : AE D)) = 1) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def InStabAt (V : HSp D) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (k : GA D V) : Prop :=
  (Formalism.L2.Theta.mt V k).map (infPart D) = 1 ∧
    (∀ w, w ≠ v → ((Formalism.L2.Theta.mt V k).map (finPart D)).map (compFin D w) = 1) ∧
    ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V k).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))

def VacFixedAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS v → CharUnramAt D χT v →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S LS → IsSelfDualC T LT →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
        IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) fun w => w = v) f →
        ∀ (k : GA D S) (k' : GA D T), InStabAt S LS v k → InStabAt T LT v k' → om (k, k') f = f

def VacFixed (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), ExtUnramAt D v → VacFixedAt D v

theorem inStabAt_one (V : HSp D) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : InStabAt V L v 1 := by
  have h : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun w _ => ?_, fun y => ?_⟩
  · rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [h, Matrix.map_one _ (map_zero _) (map_one _)]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem isLatVac_at_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f := by
  have hle : (latO S T LS LT fun w => w = v) ≤ latO S T LS LT fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro x ⟨α, hα, -, h⟩
    exact ⟨α, hα, fun w hw => absurd trivial hw, h⟩
  exact ⟨fun u hu => hf.1 u (hle hu), fun e he u hu => hf.2 e he u (hle hu)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

end
