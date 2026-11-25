module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocNoetherian
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ringKrullDim_eq_of_relDim {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  unfold relDim at h
  rw [hm] at h
  cases hd : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [hd] at h
    exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      exact absurd h (WithTop.top_ne_coe)
    | coe D =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      change (((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h
      have h := WithTop.coe_inj.mp h
      have : D = m + Fintype.card K := by omega
      rw [this]
      rfl

theorem DegZeroLocalRing.proof (h1 : DegZeroLocLocal.Statement.{u})
    (h2 : DegZeroLocNoetherian.Statement.{u}) (h3 : DegZeroLocDim.Statement.{u}) :
    DegZeroLocalRing.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  refine ⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩
  have e := h3 F K ι P hP W hW hPW
  rw [ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn,
    Nat.add_right_comm _ 1 (Fintype.card K), add_comm _ 1, Nat.cast_add 1, Nat.cast_one] at e
  exact ENat.WithBot.add_natCast_cancel.mp e

end

end GroundTheory.Heights₂.Heights.FieldNumbers
