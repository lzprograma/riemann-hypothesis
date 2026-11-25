module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality

@[expose] public section

namespace GlobalTheory.ChowExists

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem isHomogeneous_of_component {I : Ideal (MvPolynomial (Fin N) K)}
    (h : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin N) K) :=
  _root_.GlobalTheory.ConeDeg.isHomogeneous_of_component h

theorem aeval_eq_zero_of_block {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f)
    (t : Fin (D + 1) × Fin N → AlgebraicClosure K) (i : Fin (D + 1)) (ht : ∀ j, t (i, j) = 0) :
    aeval t f = 0 :=
  _root_.GlobalTheory.ConeDeg.aeval_eq_zero_of_block h t i ht

theorem not_lt_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} {D D' δ δ' : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} {f' : MvPolynomial (Fin (D' + 1) × Fin N) K}
    (h : IsChowFormInt P D δ f) (h' : IsChowFormInt P D' δ' f') : ¬ D < D' :=
  _root_.GlobalTheory.ConeDeg.not_lt_of_isChowFormInt h h'

theorem exists_X_notMem {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : ∃ j, X j ∉ P :=
  _root_.GlobalTheory.ConeDeg.exists_X_notMem h

theorem ringKrullDim_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) :=
  _root_.GlobalTheory.ConeDeg.ringKrullDim_of_isChowFormInt hP h

theorem exists_eq_coneIdeal {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {δ : ℕ}
    {f : MvPolynomial (Fin (0 + 1) × Fin N) K} (h : IsChowFormInt P 0 δ f) :
    ∃ (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 ∧ P = coneIdeal K y := by
  apply _root_.GlobalTheory.ConeDeg.exists_eq_coneIdeal <;> assumption

theorem coeff_sub_comp {H : Polynomial ℚ} {D : ℕ} (h : H.natDegree ≤ D + 1) :
    (H - H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ))).coeff D = (D + 1) * H.coeff (D + 1) :=
  _root_.GlobalTheory.ConeDeg.coeff_sub_comp h

theorem degree_eq_coeff (D : ℕ) : ∀ (K : Type) [Field K] [CharZero K] (P : Ideal (MvPolynomial (Fin N) K))
    [P.IsPrime], (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ∀ (δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f →
    (δ : ℚ) = (D.factorial : ℚ) * (idealHilbertPoly P).coeff D := by
  apply _root_.GlobalTheory.ConeDeg.degree_eq_coeff <;> assumption

theorem degree_eq_hilbertDegree [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : δ = hilbertDegree P := by
  have hP' := fun g hg n => homogeneousComponent_mem_of_mem hP (p := g) hg n
  have h1 := degree_eq_coeff D K P hP' δ f h
  rw [← cast_hilbertDegree_of_degree_eq hP
    (degree_idealHilbertPoly_eq_of_isPrime hP (ringKrullDim_of_isChowFormInt hP' h))] at h1
  exact_mod_cast h1

theorem exists_isChowFormInt [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} (hp : P.IsPrime)
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowFormInt P D (hilbertDegree P) f := by
  obtain ⟨δ, f, hf⟩ := exists_isChowFormInt_of_ringKrullDim_eq K N D P hp
    (fun g hg n => homogeneousComponent_mem_of_mem hP hg n) hD
  exact ⟨f, degree_eq_hilbertDegree hP hf ▸ hf⟩

theorem comap_map_eq {L σ : Type} [Field L] [Algebra K L] (I : Ideal (MvPolynomial σ K)) :
    (I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)).comap
      (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L) = I := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hr' : ∀ c : K, r (algebraMap K L c) = c := fun c => LinearMap.congr_fun hr c
  let ρ : MvPolynomial σ L → MvPolynomial σ K := fun p => ∑ s ∈ p.support, monomial s (r (AddMonoidAlgebra.coeff p s))
  have hρ : ∀ p s, AddMonoidAlgebra.coeff (ρ p) s = r (AddMonoidAlgebra.coeff p s) := fun p s => by
    classical
    simp only [ρ, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.1 h, map_zero]
  have hadd : ∀ p q, ρ (p + q) = ρ p + ρ q := fun p q => MvPolynomial.ext _ _ fun s => by
    simp only [hρ, MvPolynomial.coeff_add, map_add (f := _)]
  have hmul : ∀ p (g : MvPolynomial σ K), ρ (p * map (algebraMap K L) g) = ρ p * g := fun p g =>
    MvPolynomial.ext _ _ fun s => by
      classical
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hρ, coeff_mul, map_sum, coeff_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  refine le_antisymm (fun g hg => ?_) Ideal.le_comap_map
  have key : ∀ p ∈ I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L),
      ∀ q, ρ (q * p) ∈ I := fun p hp => by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact fun q => hmul q x ▸ I.mul_mem_left _ hx
    | zero =>
      intro q
      have : ρ (q * 0) = 0 := MvPolynomial.ext _ _ fun s => by simp [hρ]
      exact this ▸ I.zero_mem
    | add x y _ _ hx hy => exact fun q => by rw [mul_add, hadd]; exact I.add_mem (hx q) (hy q)
    | smul a x _ hx => exact fun q => by rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have h1 := key _ hg 1
  have h2 : ρ (1 * map (algebraMap K L) g) = g := MvPolynomial.ext _ _ fun s => by
    rw [hρ, one_mul, coeff_map, hr']
  rwa [h2] at h1

theorem exists_isChowForm [CharZero K] {I : Ideal (MvPolynomial (Fin N) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) K))
    (hp : (I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (AlgebraicClosure K))).IsPrime) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ I) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowForm I D (hilbertDegree I) f := by
  have hpI : I.IsPrime := by
    rw [← comap_map_eq (L := AlgebraicClosure K) I]
    exact Ideal.comap_isPrime _ _
  obtain ⟨f, hf⟩ := exists_isChowFormInt hpI hI hD
  refine ⟨f, hf.isChowForm ?_⟩
  obtain ⟨hE, hEH⟩ := GlobalTheory.HilbBaseChange.idealHilbertPoly_map K (AlgebraicClosure K) N I
    (fun g hg n => homogeneousComponent_mem_of_mem hI hg n)
  have hE' := isHomogeneous_of_component hE
  obtain ⟨j, hj⟩ := exists_X_notMem hf
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hE' (i := j) (fun h => hj (by
    rw [← comap_map_eq (L := AlgebraicClosure K) I, Ideal.mem_comap, map_X]
    exact h))
  have h1 := degree_idealHilbertPoly_eq_of_isPrime hE' he
  rw [hEH, degree_idealHilbertPoly_eq_of_isPrime hI hD] at h1
  obtain rfl : D = e := by exact_mod_cast h1
  obtain ⟨f', hf'⟩ := exists_isChowFormInt hp hE' he
  rw [hilbertDegree, hEH, ← hilbertDegree] at hf'
  have hdvd : f' ∣ map (algebraMap K (AlgebraicClosure K)) f := hf'.dvd_of_forall_aeval_eq_zero fun u hu => by
    obtain ⟨y, hy, h2, h3⟩ := (hf'.zero_iff u).1 hu
    rw [aeval_map_algebraMap]
    refine (hf.zero_iff_of_isAlgClosed hI u).2 ⟨y, hy, fun g hg => ?_, h3⟩
    have := h2 _ (Ideal.mem_map_of_mem _ hg)
    rwa [aeval_map_algebraMap] at this
  have hF0 : map (algebraMap K (AlgebraicClosure K)) f ≠ 0 := fun h =>
    hf.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective (h.trans (map_zero _).symm))
  have hFh := ((isMultiHomogeneous_iff_block.1 hf.homog).isHomogeneous).map (algebraMap K (AlgebraicClosure K))
  have hfh := (isMultiHomogeneous_iff_block.1 hf'.homog).isHomogeneous
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_dvd hF0 hdvd
    (by rw [hFh.totalDegree hF0, hfh.totalDegree hf'.ne_zero])
  rw [hcf]
  exact (hf'.C_mul hc).irred

end GlobalTheory.ChowExists

namespace GlobalTheory.Published

theorem chowFormIntExists_holds : ChowFormIntExists :=
  chowFormIntExists_iff.2 fun _ _ _ _ _ _ hP hp hD => GlobalTheory.ChowExists.exists_isChowFormInt hp hP hD

end GlobalTheory.Published
