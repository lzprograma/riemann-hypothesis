module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder

namespace GlobalTheory


open Classical in
theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add (f := _)]; exact a.add a'
    · simp only [map_add (f := _), Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), c, c']; rfl

end GlobalTheory
