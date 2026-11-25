module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def eW (w : InfinitePlace F) : AF F := pairA F (Pi.single w 1) 0

theorem eW_mul_self (w : InfinitePlace F) : eW w * eW w = eW w := by
  apply Prod.ext
  · funext v
    show (eW w).1 v * (eW w).1 v = (eW w).1 v
    by_cases h : v = w
    · subst h
      simp [eW, pairA]
    · simp [eW, pairA, Pi.single_eq_of_ne h]
  · show (eW w).2 * (eW w).2 = (eW w).2
    have : (eW w).2 = 0 := rfl
    rw [this, mul_zero]

theorem finOne_mul_eW (w : InfinitePlace F) : finOne F * eW w = 0 := by
  apply Prod.ext
  · funext v
    show (finOne F).1 v * (eW w).1 v = (0 : AF F).1 v
    have : (finOne F).1 v = 0 := rfl
    rw [this, zero_mul]
    rfl
  · show (finOne F).2 * (eW w).2 = (0 : AF F).2
    have : (eW w).2 = 0 := rfl
    rw [this, mul_zero]
    rfl

theorem piInf_eW {w w' : InfinitePlace F} (τ : EmbOver E w') (z : AE F E) :
    piInf τ (eW w • z) = if w' = w then piInf τ z else 0 := by
  rw [St.piInf_smul]
  by_cases h : w' = w
  · subst h
    simp [eW, pairA]
  · rw [ite_eq_right h]
    simp [eW, pairA, Pi.single_eq_of_ne h]

variable (d : SD σ)

theorem finOne_eW_smul (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : finOne F • (eW w • M) = 0 := by
  rw [smul_smul, finOne_mul_eW, zero_smul]

end PositivityTheory.SiegelWeilFormula.KAway

end
