module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntireStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEntireFactorIsThetaFunctionStandardStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

namespace GlobalTheory.FockPos

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, ite_eq_right one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, ite_eq_left rfl,
    one_mul]

theorem taylor_comp_smul' (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

theorem fock_jets_eq_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) ∧ Θ ≠ 0 ∧ ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ f hf
  have hsS := cart_one frS hS hcS
  have hsT := cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, applyAt0_monomial', applyAt0_monomial', taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

end GlobalTheory.FockPos
