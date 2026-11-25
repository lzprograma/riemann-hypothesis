module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
public import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient, Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.CoassocSimps\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

theorem atPl_eq_zero_of_common {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (w : ι) (F : Set (Module.End ℂ V)) (g : Module.End ℂ V) (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0)
    (T : ⨂[ℂ] _ : ι, V) (hT : ∀ L ∈ F, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w L T = 0) :
    GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T = 0 := by
  let hd : DecidableEq ι := inferInstance
  let contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : MultilinearMap (RingHom.id ℂ) (fun _ : ι => V) V := {
    toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
    map_update_add' := by
      intro inst x i a b
      obtain rfl : inst = hd := Subsingleton.elim _ _
      by_cases h : i = w₀
      · subst h
        have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
            ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
          Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        simp only [e, Function.update_self, smul_add]
      · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
        have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
            μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
          rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
          congr 1
          exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        simp only [e, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
    map_update_smul' := by
      intro inst x i c a
      obtain rfl : inst = hd := Subsingleton.elim _ _
      by_cases h : i = w₀
      · subst h
        have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
            ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
          Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        simp only [e, Function.update_self, RingHom.id_apply, smul_comm c]
      · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
        have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
            μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
          rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
          congr 1
          exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul, RingHom.id_apply]

  }
  let contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
    PiTensorProduct.lift (contrML w₀ μ)

  have contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
      contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
    change PiTensorProduct.lift (contrML w₀ μ) (PiTensorProduct.tprod ℂ x) = _
    rw [PiTensorProduct.lift.tprod]; rfl

  have dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
      ν (contr w₀ μ T) =
        PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
    induction T using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      congr 1
      rw [mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

  have contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
      contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
    induction T using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
        map_smul, Function.update_self, L.map_smul]
      congr 2
      exact Finset.prod_congr rfl fun k hk => by
        simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (contr w f T) = 0 := hg _ fun L hL => by
    rw [← contr_atPl, hT L hL, map_zero]
  have h := dual_contr w f (f w) (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w g T)
  rw [contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr.TensProj

open MvPolynomial Formalism.BasicNotions.TH

theorem exists_proj_of_graded {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ))
    (hK : ∀ f ∈ K, ∀ n, homogeneousComponent n f ∈ K) :
    ∃ p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ f, p f ∈ K) ∧ (∀ f ∈ K, p f = f) ∧
      ∀ f, (p f).totalDegree ≤ f.totalDegree := by
  classical
  have hex : ∀ n : ℕ, ∃ g : MvPolynomial σ ℂ →ₗ[ℂ] ↥(K ⊓ homogeneousSubmodule σ ℂ n),
      g ∘ₗ (K ⊓ homogeneousSubmodule σ ℂ n).subtype = LinearMap.id := fun n =>
    LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
  choose g hg using hex
  let q : ℕ → MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ := fun n =>
    (K ⊓ homogeneousSubmodule σ ℂ n).subtype ∘ₗ g n ∘ₗ homogeneousComponent n
  have hq0 : ∀ f : MvPolynomial σ ℂ, ∀ N, f.totalDegree < N →
      ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = ∑ i ∈ Finset.range N, q i f := by
    intro f N hN
    apply Finset.sum_subset (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
    intro i _ hi
    have : f.totalDegree < i := by simp at hi; omega
    simp [q, homogeneousComponent_eq_zero _ _ this]
  let p : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
    { toFun := fun f => ∑ i ∈ Finset.range (f.totalDegree + 1), q i f
      map_add' := fun f f' => by
        rw [hq0 f (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 f' (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          hq0 (f + f') (max (max f.totalDegree f'.totalDegree) (f + f').totalDegree + 1) (by omega),
          ← Finset.sum_add_distrib]
        simp only [map_add (f := _)]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [hq0 f (max f.totalDegree (c • f).totalDegree + 1) (by omega),
          hq0 (c • f) (max f.totalDegree (c • f).totalDegree + 1) (by omega), Finset.smul_sum]
        simp only [map_smul] }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro f
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f ∈ K
    exact Submodule.sum_mem _ fun i _ => (g i (homogeneousComponent i f)).2.1
  · intro f hf
    show ∑ i ∈ Finset.range (f.totalDegree + 1), q i f = f
    conv_rhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : homogeneousComponent i f ∈ K ⊓ homogeneousSubmodule σ ℂ i :=
      ⟨hK f hf i, homogeneousComponent_isHomogeneous i f⟩
    have := congrArg (fun h => ((h ⟨_, hm⟩ : ↥(K ⊓ homogeneousSubmodule σ ℂ i)) : MvPolynomial σ ℂ)) (hg i)
    simpa [q] using this
  · intro f
    show (∑ i ∈ Finset.range (f.totalDegree + 1), q i f).totalDegree ≤ f.totalDegree
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
    have hi' : i ≤ f.totalDegree := by simp at hi; omega
    have hh : (q i f).IsHomogeneous i := (g i (homogeneousComponent i f)).2.2
    by_cases h0 : q i f = 0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · rw [hh.totalDegree h0]; exact hi'

theorem homogeneousComponent_fockAct1 {P Q R S : ℕ} (X : Mat P Q) (hX : IsKC X) (n : ℕ) (f : Pol P Q R S) :
    homogeneousComponent n (fockAct1 P Q R S X f) = fockAct1 P Q R S X (homogeneousComponent n f) := by
  apply _root_.GlobalTheory.FockAlg.MinFirst.comp_comm <;> assumption

theorem homogeneousComponent_mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Pol P Q R S) (hf : f ∈ chiOne P Q R S x) (n : ℕ) :
    homogeneousComponent n f ∈ chiOne P Q R S x := by
  rw [mem_chiOne] at hf ⊢
  intro X hX
  rw [← homogeneousComponent_fockAct1 X hX, hf X hX, map_smul]

end GlobalTheory.KFixIrr.TensProj

namespace GlobalTheory.KFixIrr

open MvPolynomial Formalism.BasicNotions.TH TensProj

end GlobalTheory.KFixIrr

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataTheta\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

end General

end GlobalTheory.CommonQuot
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal\npublic import Mathlib.RingTheory.MvPolynomial\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Rat\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.PiTensorProduct.Finite\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.CoassocSimps\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.RealLift GlobalTheory.KFixIrr GlobalTheory.FockAlg

namespace GlobalTheory.DegKeep

section Lift

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hw_of_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ :=
  GlobalTheory.CommonQuot.map_hw L h hv

theorem joint_lift {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hL : ∀ w, IsKLieAct (a w)) (hw : ∀ w v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (a w) μ)
    (hc : ∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v))
    (W N : Submodule ℂ V) [FiniteDimensional ℂ W] (sW : ∀ w, KStable (a w) W) (sN : ∀ w, KStable (a w) N)
    (μ : ι → Ix p q → ℚ) (T : V) (hT : T ∈ W)
    (h1 : ∀ w c, a w (Eab c c) T - ((μ w c : ℚ) : ℂ) • T ∈ N) (h2 : ∀ w c d, posC c d → a w (Eab c d) T ∈ N) :
    ∃ T' ∈ W, T - T' ∈ N ∧ ∀ w, T' ∈ hwSub (a w) (μ w) := by
  have key : ∀ s : Finset ι, ∃ T' ∈ W, T - T' ∈ N ∧ ∀ w ∈ s, T' ∈ hwSub (a w) (μ w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨T, hT, by simp, by simp⟩
    | insert w s hws ih =>
      obtain ⟨T', hT'W, hTN, hT's⟩ := ih
      let Ws : Submodule ℂ V := W ⊓ ⨅ w' ∈ s, hwSub (a w') (μ w')
      have mem : ∀ v, v ∈ Ws ↔ v ∈ W ∧ ∀ w' ∈ s, v ∈ hwSub (a w') (μ w') := fun v => by
        simp only [Ws, Submodule.mem_inf, Submodule.mem_iInf]
      haveI : FiniteDimensional ℂ Ws := Submodule.finiteDimensional_of_le (inf_le_left : Ws ≤ W)
      have sWs : KStable (a w) Ws := fun Z hZ v hv => by
        rw [mem] at hv ⊢
        refine ⟨sW w Z hZ v hv.1, fun w' hw' => hw_of_comm (fun Z' v => ?_) (hv.2 w' hw')⟩
        exact hc w w' (fun e => hws (e ▸ hw')) Z Z' v
      obtain ⟨C, sC, hNC, hNCW⟩ := GlobalTheory.BlockReps.exists_compl (hL w) sWs (fun v _ => hw w v) (Ws ⊓ N) inf_le_left
        (GlobalTheory.BlockReps.stable_inf sWs (sN w))
      have hCW : C ≤ Ws := by rw [← hNCW]; exact le_sup_right
      have hT'' : T' ∈ (Ws ⊓ N) ⊔ C := by rw [hNCW, mem]; exact ⟨hT'W, hT's⟩
      obtain ⟨n, hn, c, hcC, rfl⟩ := Submodule.mem_sup.1 hT''
      have hTc : T - c ∈ N := by
        have := N.add_mem hTN hn.2
        rwa [show T - (n + c) + n = T - c by abel] at this
      have hz : ∀ v ∈ C, v ∈ N → v = 0 := fun v h h' => by
        have : v ∈ (Ws ⊓ N) ⊓ C := ⟨⟨hCW h, h'⟩, h⟩
        rwa [hNC, Submodule.mem_bot] at this
      refine ⟨c, ((mem c).1 (hCW hcC)).1, hTc, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [GlobalTheory.CommonQuot.mem_hwSub']
        refine ⟨fun d => hz _ (C.sub_mem (sC _ (GlobalTheory.CommonQuot.isKC_diag' d) c hcC) (C.smul_mem _ hcC)) ?_,
          fun d e hde => hz _ (sC _ (GlobalTheory.CommonQuot.isKC_pos' hde) c hcC) ?_⟩
        · have := N.sub_mem (h1 w' d) (N.sub_mem (sN w' _ (GlobalTheory.CommonQuot.isKC_diag' d) _ hTc)
            (N.smul_mem ((μ w' d : ℚ) : ℂ) hTc))
          rw [map_sub, smul_sub] at this
          convert this using 1; abel
        · have := N.sub_mem (h2 w' d e hde) (sN w' _ (GlobalTheory.CommonQuot.isKC_pos' hde) _ hTc)
          rw [map_sub] at this
          convert this using 1; abel
      · exact ((mem c).1 (hCW hcC)).2 w' hw'
  obtain ⟨T', h, h', h''⟩ := key Finset.univ
  exact ⟨T', h, h', fun w => h'' w (Finset.mem_univ w)⟩

end Lift

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem atPl_tprod (w : ι) (L : Module.End ℂ V) (f : ι → V) :
    atPl (V := fun _ : ι => V) w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ V) :
    atPl (V := fun _ : ι => V) w (L * L') = atPl (V := fun _ : ι => V) w L * atPl (V := fun _ : ι => V) w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp [atPl_tprod]

def actAt {p q : ℕ} (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (w : ι) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, V) where
  toFun Z := atPl (V := fun _ : ι => V) w (a Z)
  map_add' Z Z' := by rw [map_add (f := _), GlobalTheory.RealLift.Main.atPl_add]
  map_smul' c Z := by rw [map_smul, GlobalTheory.RealLift.Main.atPl_smul]; rfl

theorem actAt_apply {p q : ℕ} (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (w : ι) (Z : Mat p q) :
    actAt a w Z = atPl (V := fun _ : ι => V) w (a Z) := rfl

theorem actAt_lie {p q : ℕ} {a : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsKLieAct a) (w : ι) : IsKLieAct (actAt a w) := by
  intro Y Z hY hZ
  rw [actAt_apply, h Y Z hY hZ, actAt_apply, actAt_apply, ← atPl_mul, ← atPl_mul, sub_eq_add_neg, sub_eq_add_neg,
    GlobalTheory.RealLift.Main.atPl_add, ← neg_one_smul ℂ (a Z * a Y), GlobalTheory.RealLift.Main.atPl_smul, neg_one_smul]

def intersection_update_fsHerm_neg_one (f : ι → V) (w : ι) : V →ₗ[ℂ] ⨂[ℂ] _ : ι, V := (PiTensorProduct.tprod ℂ (s := fun _ : ι => V)).toLinearMap f w

theorem position_apply (f : ι → V) (w : ι) (v : V) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

theorem position_self (f : ι → V) (w : ι) : intersection_update_fsHerm_neg_one f w (f w) = PiTensorProduct.tprod ℂ f := by
  rw [position_apply, Function.update_eq_self]

theorem atPl_tprod_update (f : ι → V) (w : ι) (L : Module.End ℂ V) (v : V) :
    atPl (V := fun _ : ι => V) w L (intersection_update_fsHerm_neg_one f w v) = intersection_update_fsHerm_neg_one f w (L v) := by
  simp [position_apply, atPl_tprod]

theorem actAt_wts {p q : ℕ} {a : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) (w : ι)
    (T : ⨂[ℂ] _ : ι, V) : T ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt a w) μ := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Submodule.smul_mem _ _ ?_
    rw [← position_self f w]
    exact GlobalTheory.CommonQuot.map_wts (intersection_update_fsHerm_neg_one f w) (fun Z v => (atPl_tprod_update f w (a Z) v).symm) (h _)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem exists_proj (A : Submodule ℂ V) : ∃ π : Module.End ℂ V, (∀ v, π v ∈ A) ∧ ∀ v ∈ A, π v = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)
  refine ⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩
  have := congrArg (fun h => ((h ⟨v, hv⟩ : A) : V)) hg
  simpa using this

end Tensor

section Fock

open MvPolynomial

variable {P Q R S : ℕ}

theorem deg_le_of_harm {μ : Ix R S → ℚ} {f : Formalism.BasicNotions.TH.Pol P Q R S} (hh : f ∈ harm2 P Q R S)
    (hf : f ∈ hwSub (fockAct2 P Q R S) μ) : f.totalDegree ≤ ⌊degW (cPair P Q) μ⌋₊ := by
  by_cases hne : f = 0
  · simp [hne]
  obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  have hOT := GlobalTheory.BlockReps.ofType_hw GlobalTheory.FockAlg.MinFirst.kLie2 sW hP ⟨hne, hf⟩
  obtain ⟨d, hd, hhom⟩ := (harmonic_homog_of_type P Q R S).2 μ f hne hOT hh
  rw [mem_homogeneousSubmodule] at hhom
  rw [← hd, Nat.floor_natCast, hhom.totalDegree hne]

theorem stable_restrict (d : ℕ) : KStable (fockAct2 P Q R S) (restrictTotalDegree (Ln P Q R S) ℂ d) := fun Z hZ f hf => by
  rw [mem_restrictTotalDegree] at hf ⊢
  exact (LowStable.mem_nonRaising.1 (LowStable.fockAct2_mem Z hZ) f).trans hf

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

end Fock

end GlobalTheory.DegKeep

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled =====
