module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMaxHeight
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericDimBound.proof (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : AddMonoidAlgebra.coeff f 0 ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  rw [← hht, ringKrullDim_quotient P, PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩,
    ← WithBot.coe_one, ← WithBot.coe_add]
  have h1 : Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) + 1 ≤ Order.height top :=
    (add_le_add (Order.height_le_height_apply_of_strictMono g hg ⟨m, hm.isPrime⟩) le_rfl).trans
      (Order.height_add_one_le htop)
  exact (WithBot.coe_le_coe.mpr h1).trans (Order.height_le_krullDim top)

end GroundTheory.Heights₂.Heights.NumbersDVR
