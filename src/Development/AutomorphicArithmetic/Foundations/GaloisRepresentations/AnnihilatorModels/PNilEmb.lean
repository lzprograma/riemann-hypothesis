module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm, Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm", "h": "module\n\npublic import Mathlib.Algebra.Polynomial.AlgebraMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem UpperTheory.Reformulated.B.Qk66.aeval_comm :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (φ : M →ₗ[L] N) (A : Module.End L M) (A' : Module.End L N),
    (∀ (y : M), (φ : M → N) ((A : M → M) y) = (A' : N → N) ((φ : M → N) y)) →
      ∀ (Q : Polynomial L) (y : M),
        (φ : M → N) (((Polynomial.aeval A : Polynomial L → Module.End L M) Q : M → M) y) =
          ((Polynomial.aeval A' : Polynomial L → Module.End L N) Q : N → N) ((φ : M → N) y) := by
  intro L M N _ _ _ _ _ φ A A' h Q
  induction Q using Polynomial.induction_on with
  | C a =>
    intro y
    simp [Module.algebraMap_end_apply]
  | add p q hp hq =>
    intro y
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    intro y
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval A), map_mul (Polynomial.aeval A'),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V W : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
  [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]

private def ext1 (B : Type) [AddCommGroup B] [Module F B] (f : V →ₗ[L] W) : V ⊗[F] B →ₗ[L] W ⊗[F] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

private theorem scalar_extension_tmul (f : V →ₗ[L] W) (v : V) (b : B) : ext1 (F := F) B f (v ⊗ₜ b) = f v ⊗ₜ b := by
  simp [ext1]

private theorem typeCharacterExtension_mem_range_coefficientRing {ρ : Representation L G V} {ρ' : Representation L G W} {f : V →ₗ[L] W} (h : Inter ρ ρ' f)
    {x : V ⊗[F] B} (hx : x ∈ Dinv σ ρ) : ext1 B f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (ext1 B f y) =
      ext1 B f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y with
    | tmul v b => simp [scalar_extension_tmul, h g v]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, hx]

private theorem scalar_extension_period_action (f : V →ₗ[L] W) (y : V ⊗[F] B) :
    ext1 B f (onPer ψ L V y) = onPer ψ L W (ext1 B f y) := by
  induction y with
  | tmul v b => simp [scalar_extension_tmul, onPer]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem scalar_extension_basis_coord {κ : Type} [DecidableEq κ] (b : Basis κ F B) (f : V →ₗ[L] W) (y : V ⊗[F] B) (k : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (ext1 B f y) k = f (TensorProduct.equivFinsuppOfBasisRight b y k) := by
  induction y with
  | tmul v c =>
    rw [scalar_extension_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.map_smul_of_tower]
  | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]

end

theorem nilEmb_of : NilEmb := by
  intro F G B _ _ _ _ σ ψ L _ _ V _ _ _ _ ρ I _ W _ _ _ _ ρ' f hI hinj Q hQ
  classical
  cases nonempty_fintype I
  choose N hN using hQ
  refine ⟨∑ i, N i, fun x hx => ?_⟩
  set A := Polynomial.aeval (onPer ψ L V) Q with hA
  have hzero : ∀ i, ext1 B (f i) ((A ^ ∑ i, N i) x) = 0 := by
    intro i
    have hle : N i ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hA, ← map_pow, _root_.UpperTheory.Reformulated.B.Qk66.aeval_comm _ _ _
        (scalar_extension_period_action ψ (f i)) (Q ^ ∑ i, N i),
      map_pow, ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply,
      hN i _ (typeCharacterExtension_mem_range_coefficientRing σ (hI i) hx), map_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight (Basis.ofVectorSpace F B)).injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hinj _ fun i => ?_
  rw [← scalar_extension_basis_coord, hzero i, map_zero, Finsupp.zero_apply]

end UpperTheory.Gal.crystallineComparison
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb =====
