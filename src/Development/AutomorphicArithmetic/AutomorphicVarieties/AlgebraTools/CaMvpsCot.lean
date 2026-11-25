module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
import Mathlib.RingTheory.MvPowerSeries.Equiv

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (σ : Type) [Fintype σ], IsRegularLocalRing (MvPowerSeries σ O) ∧
        ringKrullDim (MvPowerSeries σ O) = ((Fintype.card σ + 1 : ℕ) : WithBot ℕ∞) ∧
        CotInd (MvPowerSeries σ O) (fun o : Option σ => o.elim (MvPowerSeries.C ϖ) MvPowerSeries.X) := by
  intro O _ _ _ ϖ hϖ σ _
  have hreg : IsRegularLocalRing (MvPowerSeries σ O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O σ
  have hdim : ringKrullDim (MvPowerSeries σ O) = ((Fintype.card σ + 1 : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, add_comm]
    push_cast
    rfl
  have hm : maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  refine ⟨hreg, hdim, cotInd_of_span _ _ _ ?_ ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨o, rfl⟩
      refine GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_
      cases o with
      | none => simpa using hϖ.not_isUnit
      | some i => simp
    · intro f hf
      have h0 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hf
      rw [hm, Ideal.mem_span_singleton] at h0
      obtain ⟨c, hc⟩ := h0
      have h1 : f - MvPowerSeries.C (ϖ * c) ∈
          Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
        refine _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X Finset.univ _ fun n hn => ?_
        have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
        subst this
        simp [hc]
      have h2 : f = (f - MvPowerSeries.C (ϖ * c)) + MvPowerSeries.C ϖ * MvPowerSeries.C c := by
        rw [map_mul]; ring
      rw [h2]
      refine add_mem (Ideal.span_mono ?_ h1)
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨none, rfl⟩))
      rintro _ ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
  · have h := hreg.spanFinrank_maximalIdeal
    rw [hdim] at h
    rw [Fintype.card_option]
    have h' : (maximalIdeal (MvPowerSeries σ O)).spanFinrank = Fintype.card σ + 1 := by
      exact_mod_cast h
    exact h'.ge
