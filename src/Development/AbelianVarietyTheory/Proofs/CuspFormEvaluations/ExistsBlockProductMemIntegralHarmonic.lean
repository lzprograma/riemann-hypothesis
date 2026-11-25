module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorMonomials
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA

@[expose] public section

noncomputable section

namespace GlobalTheory.BlockProdEx

section Minors

open MvPolynomial Formalism.L2.Pj

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k]
  (col : ∀ σ, ∀ s : Fin (r σ), Fin (s + 1) → Fin n)

theorem minorMonomial_isHomogeneous (a : T → ℕ → ℕ) :
    (minorsP r n col k a).IsHomogeneous (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col (fun _ => 1) σ' s).pow (a σ' s - a σ' (s + 1))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    mul_comm (a _ _ - a _ _)] at h
  exact h

theorem minors_polynomial_coefficient_norm_le_pow (a : T → ℕ → ℕ) (N : ℕ) (hN : ∀ σ, r σ ≤ N) :
    MvPoly.l1Norm (minorsP r n col ℂ a) ≤
      (N : ℝ) ^ (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine (MvPoly.l1Norm_prod_le _ _).trans
    (Finset.prod_le_prod₀ (fun _ _ => MvPoly.l1Norm_nonneg _) fun σ _ => ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  simp only [pow_mul]
  refine MvPoly.l1Norm_prod_pow_le _ _ _ _ fun s _ => ?_
  refine (MvPoly.l1Norm_det_le_pow _ (R := 1) fun i j => by simp).trans ?_
  rw [Fintype.card_fin, mul_one]
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
  exact_mod_cast (Nat.succ_le_of_lt s.isLt).trans (hN σ)

theorem exists_cols (h : ∑ σ, r σ * (r σ + 1) ≤ 2 * n) :
    ∃ e : (Σ x : (Σ σ, Fin (r σ)), Fin (x.2 + 1)) → Fin n, Function.Injective e := by
  have hc : Fintype.card (Σ x : (Σ σ, Fin (r σ)), Fin (x.2 + 1)) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    have : ∀ m : ℕ, 2 * ∑ s : Fin m, ((s : ℕ) + 1) = m * (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [mul_add, ih]; ring
    rw [← Finset.sum_congr rfl fun σ _ => this (r σ), ← Finset.mul_sum] at h
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨e, e.injective⟩

end Minors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn

section Count

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem inPsi_conjugate_of_not {τ : E →+* ℂ} (h : ¬ InPsi H τ) : InPsi H (ComplexEmbedding.conjugate τ) := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]; simp
  have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h3, map_neg, (ThetaClaimsCompare.rt0_conj_neg_ne_zero H).1, neg_neg]

theorem sum_mult_le (Dw : Datum H) :
    ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ + 1) ≤ I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) := by
  have h1 := Equiv.sum_comp (ComplexEmbedding.involutive_conjugate (K := E)).toPerm
    (fun τ => Dw.mult τ * (Dw.mult τ + 1))
  have h2 : ∑ τ : E →+* ℂ, (Dw.mult τ * (Dw.mult τ + 1) +
      Dw.mult (ComplexEmbedding.conjugate τ) * (Dw.mult (ComplexEmbedding.conjugate τ) + 1)) ≤
      ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) := by
    refine Finset.sum_le_sum fun τ _ => ?_
    by_cases h : InPsi H τ
    · rw [ThetaClaimsCompare.mult_of_inPsi h,
        ThetaClaimsCompare.mult_of_not_inPsi (ThetaClaimsCompare.not_inPsi_conjugate h)]
      nlinarith [Nat.zero_le (Dw.p * Dw.q)]
    · rw [ThetaClaimsCompare.mult_of_not_inPsi h,
        ThetaClaimsCompare.mult_of_inPsi (inPsi_conjugate_of_not h)]
      nlinarith [Nat.zero_le (Dw.p * Dw.q)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card E ℂ, smul_eq_mul] at h2
  simp only [Function.Involutive.coe_toPerm] at h1
  rw [h1] at h2
  have h3 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hm := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h4 : Module.finrank ℚ E = 2 * I2.PT.f E := by
    unfold I2.PT.f
    rw [h3] at hm
    omega
  rw [h4, Nat.mul_assoc] at h2
  rw [Nat.mul_assoc]
  omega

theorem isBlockProd_minorsP (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K]
    (e : (Σ x : (Σ σ, Fin (Dw.mult σ)), Fin (x.2 + 1)) → Fin n) (he : Function.Injective e)
    (a : (E →+* ℂ) → ℕ → ℕ) :
    IsBlockProd (Dw := Dw) (minorsP Dw.mult n (fun σ s j => e ⟨⟨σ, s⟩, j⟩) K a) := by
  classical
  let I := {x : (Σ σ, Fin (Dw.mult σ)) // 1 ≤ a x.1 x.2 - a x.1 (x.2 + 1)}
  let bk : I → Bk Dw n := fun x =>
    { τ := x.1.1, i := x.1.2 + 1, hi := x.1.2.isLt, c := a x.1.1 x.1.2 - a x.1.1 (x.1.2 + 1), hc := x.2,
      col := fun j => e ⟨x.1, j⟩,
      col_inj := fun j j' h => eq_of_heq (Sigma.mk.inj_iff.1 (he h)).2 }
  refine ⟨Fintype.card I, fun j => bk ((Fintype.equivFin I).symm j), fun j j' hj u u' h => ?_, ?_⟩
  · exact hj ((Fintype.equivFin I).symm.injective (Subtype.ext (congrArg Sigma.fst (he h))))
  · rw [Equiv.prod_comp (Fintype.equivFin I).symm (fun x => (bk x).poly K), minorsP, ← Fintype.prod_sigma']
    rw [← Finset.prod_filter_of_ne (p := fun x : (Σ σ, Fin (Dw.mult σ)) => 1 ≤ a x.1 x.2 - a x.1 (x.2 + 1))]
    · exact Finset.prod_subtype _ (by simp) _
    · intro x _ hx
      by_contra h0
      exact hx (by rw [show a x.1 x.2 - a x.1 (x.2 + 1) = 0 by omega, pow_zero])

end Count

theorem exists_blockProd_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ i k, i ≤ k → a (τ, k) ≤ a (τ, i)) → I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * n → ∃ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA c a n ∧ IsBlockProd P ∧ P.totalDegree = Formalism.L2.Pj.DF Dw a ∧ ∀ σ : c.F →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) ^ Formalism.L2.Pj.DF Dw a := by
  intro E _ _ _ H Dw l c a n ha hn
  obtain ⟨e, he⟩ := exists_cols Dw.mult n ((sum_mult_le Dw).trans hn)
  let col : ∀ σ, ∀ s : Fin (Dw.mult σ), Fin (s + 1) → Fin n := fun σ s j => e ⟨⟨σ, s⟩, j⟩
  let b : (E →+* ℂ) → ℕ → ℕ := fun τ i => ThetaClaimsCompare.trunc Dw a (τ, i)
  have hinj : ∀ σ s, Function.Injective (col σ s) :=
    fun σ s j j' h => eq_of_heq (Sigma.mk.inj_iff.1 (he h)).2
  have hdis : ∀ τ, InPsi H τ → ∀ s s' i j, col τ s i ≠ col (ComplexEmbedding.conjugate τ) s' j := by
    intro τ h s s' i j hij
    have h1 : τ = ComplexEmbedding.conjugate τ := congrArg (fun x => x.1.1) (he hij)
    exact ThetaClaimsCompare.not_inPsi_conjugate h (h1 ▸ h)
  have hdeg : RowDeg Dw.mult n c.F b (minorsP Dw.mult n col c.F b) :=
    minorMonomial_rowDegree _ _ _ _ _ (ThetaClaimsCompare.antitone_trunc fun τ i j hij => ha τ i j hij)
      fun τ => ite_eq_right (lt_irrefl _)
  have hne := minorMonomial_ne_zero Dw.mult n c.F col hinj b
  have hD : (minorsP Dw.mult n col c.F b).totalDegree = Formalism.L2.Pj.DF Dw a := by
    rw [← ThetaClaimsCompare.df_trunc]
    exact (isHomogeneous_of_rowDeg hdeg).totalDegree hne
  refine ⟨minorsP Dw.mult n col c.F b, ?_, isBlockProd_minorsP Dw c.F e he b, hD, fun σ => ?_⟩
  · rw [← ThetaClaimsCompare.harmA_trunc]
    exact ⟨⟨minorMonomial_mem_harmonic _ _ _ _ _ _ hdis _, minorMonomial_rowInvariant _ _ _ _ _, hdeg⟩, minorMonomial_coeff_mem _ _ _ _ _ _⟩
  · rw [← MvPoly.l1Norm_map, minorMonomial_map, ← hD, (minorMonomial_isHomogeneous Dw.mult n c.F col b).totalDegree hne]
    refine minors_polynomial_coefficient_norm_le_pow _ _ _ _ _ fun τ => ?_
    unfold Datum.mult
    split_ifs <;> omega

end GlobalTheory.BlockProdEx
