module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem ConservationOfNumberLE.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u}) :
    ConservationOfNumberLE.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP hnt hdim a

  have hPprime : P.IsPrime := hP.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hnt, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]

  have hsp : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    ENat.WithBot.add_one_le_natCast_iff.mp ((special_dim_add_one_le hϖ P hnt).trans hdim)
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom) hsp a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
