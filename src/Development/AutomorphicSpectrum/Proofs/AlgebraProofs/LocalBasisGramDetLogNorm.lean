module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDual
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferent
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe
import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofinite

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite, Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock, Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm

-- ===== clump member: Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram\npublic import Mathlib.Algebra.AffineMonoid.Basic\npublic import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian\npublic import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDual\npublic import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans\nimport Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := @_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite

end PositivityTheory.Xgf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite =====

-- ===== clump member: Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition\npublic import Mathlib.Algebra.AffineMonoid.Basic\npublic import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement\npublic import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferent\npublic import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator\npublic import Development.WeilBound.CoreStatements.SesquilinearFractions.GramDetNeZeroLocalBasisCofinite\nimport Mathlib.Analysis.Normed.Field.Basic\nimport Mathlib.LinearAlgebra.Matrix.Determinant.Basic\nimport Mathlib.Topology.MetricSpace.Ultra.Basic\nimport Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe\nimport Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_local_basis_eq_rank (D : Datum H) {I : Type} [Fintype I] (x : I → D.La) (ℓ : ℕ) (h : IsLocBasis (𝓞 E) ℓ x) :
    Fintype.card I = D.p + D.q := by
  haveI := D.fin
  haveI := D.proj
  obtain ⟨hli, n, hn, hspan⟩ := h
  have hn0 : (n : 𝓞 E) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero ℓ)
    exact_mod_cast this
  rw [← D.rank]
  apply le_antisymm
  · exact hli.fintype_card_le_finrank
  · let g : D.La →ₗ[𝓞 E] Submodule.span (𝓞 E) (Set.range x) :=
      LinearMap.codRestrict _ ((n : 𝓞 E) • LinearMap.id) (fun y => by
        simpa [Nat.cast_smul_eq_nsmul] using hspan y)
    have hg : Function.Injective g := by
      intro y z hyz
      have h1 : (n : 𝓞 E) • y = (n : 𝓞 E) • z := congrArg Subtype.val hyz
      exact smul_right_injective _ hn0 h1
    calc Module.finrank (𝓞 E) D.La ≤ Module.finrank (𝓞 E) (Submodule.span (𝓞 E) (Set.range x)) :=
          LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card I := finrank_span_eq_card hli

theorem local_basis_gram_det_log (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes)
    (hx : IsLocBasis (𝓞 E) ℓ x) (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) :
    (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ =
      -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  classical
  have hcard := card_local_basis_eq_rank D x ℓ hx
  obtain ⟨hdet, -⟩ := PositivityTheory.Xgf.gram_det_ne_zero_local_basis_cofinite E H D _ x hcard hx.1
  obtain ⟨-, -, -, -, -, hskew, hdiff⟩ := sesq_sesquilinear_properties D
  have h21 : ∀ a b, sesq D (x (.inr a)) (x (.inl b)) = 0 := by
    intro a b
    rw [hskew (x (.inl b)) (x (.inr a)), horth]
    simp
  have hblock : gramE D x =
      Matrix.fromBlocks (gramE D (x ∘ Sum.inl)) 0 0 (gramE D (x ∘ Sum.inr)) := by
    ext (a | a) (b | b) <;> simp [gramE, horth, h21]
  have hdetprod : (gramE D x).det =
      (gramE D (x ∘ Sum.inl)).det * (gramE D (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁]
  have h1ne : (gramE D (x ∘ Sum.inl)).det ≠ 0 := fun h0 => hdet (by rw [hdetprod, h0, zero_mul])
  have h2ne : (gramE D (x ∘ Sum.inr)).det ≠ 0 := fun h0 => hdet (by rw [hdetprod, h0, mul_zero])
  refine ⟨h2ne, fun j => ?_⟩
  set emb : 𝓞 E →+* ℂ_[ℓ] := j.comp (algebraMap (𝓞 E) E) with hemb_def
  have hemb : Function.Injective emb := j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0, -, hL⟩ := _root_.PositivityTheory.Xgf.padic_logIdeal_max_element E ℓ emb _ hemb hne
  have hemba : emb a = j (a : E) := rfl
  have hja : 0 < ‖j (a : E)‖ := by
    rw [← hemba]
    exact norm_pos_iff.mpr ((map_ne_zero_iff emb hemb).mpr ha0)
  set R : ℝ := ‖j (a : E)‖⁻¹ with hR
  have hR0 : 0 < R := inv_pos.mpr hja
  have hent : ∀ y z : D.La, ‖j (sesq D y z)‖ ≤ R := by
    intro y z
    obtain ⟨b, hb⟩ := hdiff a ha y z
    have hb1 : ‖j (b : E)‖ ≤ 1 :=
      (_root_.GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator E ℓ (b : E)).mpr ⟨1, b, Nat.Prime.not_dvd_one ℓ.prop, by simp⟩ j
    have hm : ‖j (a : E)‖ * ‖j (sesq D y z)‖ ≤ 1 := by
      rw [← norm_mul, ← map_mul, hb]
      exact hb1
    calc ‖j (sesq D y z)‖ = ‖j (a : E)‖⁻¹ * (‖j (a : E)‖ * ‖j (sesq D y z)‖) := by
          field_simp
      _ ≤ ‖j (a : E)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hja.le)
      _ = R := mul_one _
  have hbound : ∀ {I : Type} [Fintype I] [DecidableEq I] (y : I → D.La),
      ‖j (gramE D y).det‖ ≤ R ^ Fintype.card I := by
    intro I _ _ y
    rw [RingHom.map_det]
    exact _root_.GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric ℂ_[ℓ] I _ R hR0.le (fun a b => by
      simpa [RingHom.mapMatrix_apply, gramE] using hent (y a) (y b))
  have hu := hbound (x ∘ Sum.inl)
  have hv := hbound (x ∘ Sum.inr)
  simp only [Fintype.card_fin] at hu hv
  have hfull := _root_.GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE E H D _ x ℓ hx j
  rw [← hemb_def, hL, hemba] at hfull
  have hu0 : 0 < ‖j (gramE D (x ∘ Sum.inl)).det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h1ne)
  have hv0 : 0 < ‖j (gramE D (x ∘ Sum.inr)).det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h2ne)
  have huv : ‖j (gramE D (x ∘ Sum.inl)).det‖ * ‖j (gramE D (x ∘ Sum.inr)).det‖ = R ^ (p + q) := by
    have hlog : Real.log (‖j (gramE D (x ∘ Sum.inl)).det‖ * ‖j (gramE D (x ∘ Sum.inr)).det‖) =
        Real.log (R ^ (p + q)) := by
      rw [← norm_mul, ← map_mul, ← hdetprod, hfull, Real.log_pow, hR, Real.log_inv]
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast
      ring
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hu0 hv0)) (Set.mem_Ioi.mpr (pow_pos hR0 _)) hlog
  have hge : R ^ q ≤ ‖j (gramE D (x ∘ Sum.inr)).det‖ := by
    have hp0 : 0 < R ^ p := pow_pos hR0 _
    have : R ^ p * R ^ q ≤ R ^ p * ‖j (gramE D (x ∘ Sum.inr)).det‖ := by
      rw [← pow_add, ← huv]
      exact mul_le_mul_of_nonneg_right hu hv0.le
    exact le_of_mul_le_mul_left this hp0
  rw [hL, hemba, le_antisymm hv hge, Real.log_pow, hR, Real.log_inv]
  ring

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem local_basis_gram_det_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ = -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
  fun _ _ _ _ _ D p q x ℓ hx horth => GlobalTheory.CompanionTheory.Ar.Fl.local_basis_gram_det_log D p q x ℓ hx horth

end PositivityTheory.Xgf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm", "h": "module\n\npublic import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition\npublic import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes\npublic import Mathlib.Algebra.AffineMonoid.Basic\npublic import Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDetLogNorm =====
