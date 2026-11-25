module

import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Formalism.PeriodIntegrals.DSInfCharCap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliFreeAction

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  intros
  apply _root_.UpperTheory.V.Fb.map_qdet <;> assumption

theorem actU_qdet : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  intro n ε H _ _ σ S E hE u v
  let F : FreeMonoid (Fin n × Fin n) →* Module.End ℂ S := FreeMonoid.lift fun ab => E ab.1 ab.2
  let ψ : MonoidAlgebra ℂ (FreeMonoid (Fin n × Fin n)) →ₐ[ℂ] Module.End ℂ S :=
    MonoidAlgebra.lift ℂ _ _ F
  let φ : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ S :=
    ψ.comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ (Fin n × Fin n) ≃ₐ[ℂ] _).toAlgHom
  have hw : ∀ l : List (Fin n × Fin n),
      PI.DSInfCharCap.dsigCW ε σ (l.map PI.DSInfCharCap.unitM) (v : H) =
        ((F (FreeMonoid.ofList l) v : S) : H) := by
    intro l
    induction l with
    | nil => simp [PI.DSInfCharCap.dsigCW]
    | cons a l ih =>
      rw [List.map_cons, PI.DSInfCharCap.dsigCW, ih, FreeMonoid.ofList_cons, map_mul,
        Module.End.mul_apply, ← hE a.1 a.2]
      simp [F]
  have hφ : ∀ p, PI.DSInfCharCap.actU ε σ p v = ((φ p v : S) : H) := by
    intro p
    have : φ p = ψ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := rfl
    rw [this]
    simp only [ψ, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, Finsupp.sum,
      LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hw]
  have hE' : (fun a b => φ (PI.DSInfCharCap.Egl n a b)) = E := by
    funext a b
    simp [φ, ψ, F, PI.DSInfCharCap.Egl, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hφ, map_qdet, hE']

end GlobalTheory.CapelliFreeAction
