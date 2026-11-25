module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cm_of_regular (A : Type) [CommRing A] [IsRegularLocalRing A] : ReciprocityTheory.CA.IsCM A := by
  obtain ⟨xs, hspan, hlen, hreg⟩ :=
    PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  refine ⟨inferInstance, xs.length, hlen.symm, xs, rfl, fun r hr => ?_, hreg⟩
  rw [← hspan]
  exact Ideal.subset_span hr

theorem UpperTheory.V.CA.cl_cm :
    (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (d : ℕ), IsCM (MvPowerSeries (Fin d) O) ∧ ringKrullDim (MvPowerSeries (Fin d) O) = (d + 1 : ℕ)) ∧ ∀ (k : Type) [Field k] (d : ℕ), IsCM (MvPowerSeries (Fin d) k) ∧ ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  refine ⟨fun O _ _ _ _ d => ⟨?_, ?_⟩, fun k _ d => ⟨?_, ?_⟩⟩
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) O) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    push_cast
    rfl
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
