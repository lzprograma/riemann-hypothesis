module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimple

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem minpoly_eval_zero_ne_zero {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by
  intro h0
  have h1 : f.HasEigenvalue 0 := End.hasEigenvalue_iff_isRoot.mpr h0
  exact spectrum.zero_notMem ℂ hf (End.hasEigenvalue_iff_mem_spectrum.mp h1)

theorem isSemisimple_of_pow {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by
  have hsep : (minpoly ℂ (g ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have h0 := minpoly_eval_zero_ne_zero (hg.pow m)
  set p := minpoly ℂ (g ^ m) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := expand ℂ m p)
    (Separable.squarefree ?_) ?_
  · rw [Separable, derivative_expand]
    refine IsCoprime.mul_right (IsCoprime.map hsep (expand ℂ m).toRingHom)
      (IsCoprime.mul_right ?_ (IsCoprime.pow_right ?_))
    · have : IsUnit ((m : ℕ) : ℂ[X]) := by
        rw [← C_eq_natCast]
        exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hm.ne'))
      exact (isCoprime_mul_unit_left_right this _ 1).mpr isCoprime_one_right |>.of_mul_right_left
    · refine ((irreducible_X.coprime_iff_not_dvd).mpr ?_).symm
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, expand_eval, zero_pow hm.ne']
      exact h0
  · rw [expand_aeval]
    exact minpoly.aeval ℂ _

end GlobalTheory.WeilDeligne.FrobSemisimple

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in
private theorem isSemisimple_of_mul_eq_one' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} (hf : f.IsSemisimple) (hgf : g * f = 1) :
    g.IsSemisimple := by
  apply _root_.GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  have htop : ⨆ α, f.eigenspace α = ⊤ :=
    hf.iSup_maxGenEigenspace_eq_top_iff.1 (Module.End.iSup_maxGenEigenspace_eq_top f)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun α => le_trans ?_ (le_iSup _ α⁻¹)
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : v = α • g v := by
    have := congrArg g hv
    rwa [← Module.End.mul_apply, hgf, Module.End.one_apply, map_smul] at this
  by_cases hα : α = 0
  · subst hα
    rw [zero_smul] at h1
    simp [h1]
  · conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ φ hφ hss σ
  have hunit : IsUnit (ρ σ) := (Group.isUnit σ).map ρ
  obtain ⟨τ, hτdeg, hτ⟩ : ∃ τ : _root_.GlobalTheory.WeilDeligne.Weil h,
      _root_.GlobalTheory.WeilDeligne.deg τ = _root_.GlobalTheory.WeilDeligne.deg σ ∧ End.IsSemisimple (ρ τ) := by
    rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨φ ^ k, by rw [_root_.GlobalTheory.WeilDeligne.deg_pow, hφ, hk]; ring, ?_⟩
      rw [map_pow]
      exact hss.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hd.le
      have hinv : End.IsSemisimple (ρ φ⁻¹) :=
        isSemisimple_of_mul_eq_one' hss (by rw [← map_mul, inv_mul_cancel, map_one])
      refine ⟨φ⁻¹ ^ k, ?_, ?_⟩
      · rw [_root_.GlobalTheory.WeilDeligne.deg_pow, ← zpow_neg_one, _root_.GlobalTheory.WeilDeligne.deg_zpow, hφ, hk]
        ring
      · rw [map_pow]
        exact hinv.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
  obtain ⟨m, hm, hpow⟩ :=
    _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ σ τ hτdeg.symm
  apply FrobSemisimple.isSemisimple_of_pow hunit hm
  rw [hpow]
  exact hτ.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) m)

end GlobalTheory.WeilDeligne
