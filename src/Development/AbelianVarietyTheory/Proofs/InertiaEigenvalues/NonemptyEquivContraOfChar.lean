module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.CStarAlgebra.Classes\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

end GlobalTheory.LocGL.ProjLine
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn\npublic import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Order.Hom.Esakia\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology
open scoped OnePoint

namespace GlobalTheory.LocGL

namespace ProjLine

section General

variable {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X]
  [Module ℂ X] {σ : Representation ℂ G W} {π : Representation ℂ G V}

def quot (S : Subrepresentation π) : Representation ℂ G (V ⧸ S.toSubmodule) :=
  π.quotient _ fun g _ hv => S.apply_mem_toSubmodule g hv

def quotMk (S : Subrepresentation π) : π.IntertwiningMap (quot S) := ⟨S.toSubmodule.mkQ, fun _ => rfl⟩

theorem isCosocle_quot {L : Subrepresentation π} (h0 : L ≠ ⊤) (h : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤) :
    IsCosocle (quot L) π := by
  have hk : (quotMk L).ker = L := SetLike.ext fun v => Submodule.Quotient.mk_eq_zero _
  refine ⟨?_, quotMk L, L.toSubmodule.mkQ_surjective, fun S hS => ?_⟩
  · have h1 : L.toSubmodule ≠ ⊤ := fun e => h0 (Subrepresentation.toSubmodule_injective e)
    have := Submodule.Quotient.nontrivial_iff.2 h1
    have : Nontrivial (Subrepresentation (quot L)) := ⟨⊥, ⊤, fun e =>
      bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
    refine ⟨fun T => ?_⟩
    let T' : Subrepresentation π := ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
    refine (h T').imp (fun e => eq_bot_iff.2 fun y hy => ?_) fun e => eq_top_iff.2 fun y _ => ?_
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      exact (Submodule.Quotient.mk_eq_zero _).2 (e hy)
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      have : v ∈ T' := e ▸ trivial
      exact this
  · rw [hk]
    exact ((hS.le_iff.1 ((h S).resolve_right hS.1)).resolve_left h0).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem nonempty_equiv_contra_ofChar {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) :
    Nonempty ((ofChar χ⁻¹).Equiv (contra (ofChar χ))) := by
  have key : ∀ (c : ℂ) g, (ofChar χ).dual g (c • LinearMap.id) = ((χ g)⁻¹ * c : ℂ) • LinearMap.id := fun c g =>
    LinearMap.ext fun v => by
      show c • ofChar χ (g⁻¹ : G) v = _
      rw [ofChar_apply]
      simp [mul_left_comm, mul_assoc]
  let f : (ofChar χ⁻¹).IntertwiningMap (contra (ofChar χ)) :=
    { toFun := fun c => ⟨c • LinearMap.id, mem_smoothPart_of_nhds (Filter.mem_of_superset (hχ.mem_nhds (one_mem _))
        fun g hg => by
          have hg' : χ g = 1 := hg
          rw [Set.mem_ofPred_eq, key, hg']
          simp)⟩
      map_add' := fun c d => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c d => Subtype.ext (mul_smul _ _ _)
      isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (Eq.trans (by simp) (key c g).symm) }
  refine ⟨equivOfBijective f ⟨fun c d h => ?_, fun l => ⟨l.1 1, Subtype.ext (LinearMap.ext fun v => ?_)⟩⟩⟩
  · simpa [f] using congrArg (fun l => l.1 1) h
  · show l.1 1 • v = l.1 v
    rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [DecidableEq k]


variable (k) in
def funRep : Representation ℂ (GL (Fin 2) k) (OnePoint k → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (g⁻¹ • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
@[simp] theorem funRep_apply (g : GL (Fin 2) k) (F : OnePoint k → ℂ) (x : OnePoint k) :
    funRep k g F x = F (g⁻¹ • x) := rfl

def pts : (Σ _ : Fin 2, Fin 1) ≃ Fin 2 := stdBlocks (fun _ => 1) (by simp)

theorem pts_apply (a : Fin 2) (i : Fin 1) : pts ⟨a, i⟩ = a :=
  Fin.ext ((stdBlocks_val (fun _ => 1) _ a i).trans (by simp))


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_parab_pts {g : GL (Fin 2) k} : g ∈ parab k pts ↔ g • (∞ : OnePoint k) = ∞ := by
  rw [OnePoint.smul_infty_eq_self_iff, mem_parab_iff]
  simp only [pts_apply]
  refine ⟨fun h => h 1 0 0 0 (by simp), fun h a b _ _ hab => ?_⟩
  fin_cases a <;> fin_cases b <;> simp at hab
  exact h


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_smul_infty (x : OnePoint k) : ∃ g : GL (Fin 2) k, g⁻¹ • (∞ : OnePoint k) = x := by
  induction x using OnePoint.rec with
  | infty => exact ⟨1, by simp⟩
  | coe x => exact ⟨(GeneralLinearGroup.mkOfDetNeZero !![x, 1; 1, 0] (by simp))⁻¹, by simp [OnePoint.smul_infty_eq_ite]⟩


omit [DecidableEq k] in
theorem law_detLevi (η : kˣ →* ℂˣ) (p : parab k pts) (c : ℂ) :
    twist (ofChar (detLevi pts η)) (deltaHalf k _) (leviProj k pts p) c = (detChar (Fin 2) η p : ℂ) * c := by
  have : GeneralLinearGroup.det (leviEmb k pts (leviProj k pts p)) =
      GeneralLinearGroup.det (p : GL (Fin 2) k) := by
    classical
    let g := leviProj k pts p
    have hm : leviEmb k pts g ∈ parab k pts := by
      apply mem_parab_iff.2
      intro a b i j hab
      simp [leviEmb, Matrix.blockDiagonal'_apply_ne, hab.ne']
    have hp : leviProj k pts ⟨leviEmb k pts g, hm⟩ = g := by
      funext a
      ext i j
      simp [leviProj, diagBlock, leviEmb, Matrix.blockDiagonal'_apply_eq]
    have h := det_parab k pts ⟨leviEmb k pts g, hm⟩
    rw [hp] at h
    exact h.trans (det_parab k pts p).symm
  simp [detLevi, this, mul_assoc, mul_left_comm (deltaHalf k _ (leviProj k pts p) : ℂ)]

theorem nonempty_equiv_parInd {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    Nonempty ((twist (smoothRep (funRep k)) (detChar _ η)).Equiv (parInd pts (ofChar (detLevi pts η)))) := by
  have hU : ∀ᶠ g in 𝓝 (1 : GL (Fin 2) k), detChar (Fin 2) η g = 1 := hη.detChar.mem_nhds (one_mem _)
  let f : (twist (smoothRep (funRep k)) (detChar _ η)).IntertwiningMap (parInd pts (ofChar (detLevi pts η))) :=
    { toFun := fun F => ⟨⟨fun g => (detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • ∞), fun p g => by
          refine Eq.trans ?_ (law_detLevi η p _).symm
          beta_reduce
          rw [_root_.mul_inv_rev, mul_smul, mem_parab_pts.1 (inv_mem p.2), map_mul, Units.val_mul, mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hU, IsOpen.mem_nhds F.2 (by simp)] with g h1 h2
          refine Subtype.ext (funext fun x => ?_)
          show (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞) = (detChar (Fin 2) η x : ℂ) * F.1 (x⁻¹ • ∞)
          rw [map_mul, h1, mul_one, _root_.mul_inv_rev, mul_smul]
          exact congrArg _ (congrFun h2 _))⟩
      map_add' := fun F F' => Subtype.ext (Subtype.ext (funext fun x => mul_add _ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => mul_left_comm _ _ _))
      isIntertwining' := fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => by
        show (detChar (Fin 2) η x : ℂ) * ((detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • x⁻¹ • ∞)) =
          (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞)
        rw [map_mul, _root_.mul_inv_rev, mul_smul, Units.val_mul, mul_assoc])) }
  refine ⟨equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun F h => Subtype.ext (funext fun x => ?_), fun φ => ?_⟩⟩
  · obtain ⟨g, rfl⟩ := exists_smul_infty x
    exact (mul_eq_zero.1 (congrArg (fun φ => φ.1.1 g) h)).resolve_left (Units.ne_zero _)
  · choose s hs using exists_smul_infty (k := k)
    let F : OnePoint k → ℂ := fun x => (detChar (Fin 2) η (s x) : ℂ)⁻¹ * φ.1.1 (s x)
    have hF : ∀ g : GL (Fin 2) k, F (g⁻¹ • ∞) = (detChar (Fin 2) η g : ℂ)⁻¹ * φ.1.1 g := fun g => by
      have h1 : s (g⁻¹ • ∞) * g⁻¹ ∈ parab k pts := mem_parab_pts.2 (by
        rw [mul_smul, smul_eq_iff_eq_inv_smul, hs])
      have h2 := (φ.1.2 ⟨_, h1⟩ g).trans (law_detLevi η _ _)
      simp only [inv_mul_cancel_right, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at h2
      simp only [F, h2]
      field_simp
    refine ⟨⟨F, mem_smoothPart_of_nhds ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    · filter_upwards [hU, IsOpen.mem_nhds φ.2 (by simp)] with g h1 h2
      funext x
      obtain ⟨y, rfl⟩ := exists_smul_infty x
      rw [funRep_apply, ← mul_smul, ← _root_.mul_inv_rev, hF, hF, map_mul, h1, mul_one]
      exact congrArg _ (congrArg (fun φ => φ.1 y) h2)
    · show (detChar (Fin 2) η g : ℂ) * F (g⁻¹ • ∞) = _
      rw [hF, mul_inv_cancel_left₀ (Units.ne_zero _)]



omit [DecidableEq k] in
theorem exists_equiv_prodIrr {θ : Fin 2 → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin 2 → IrrGL (k := k)}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) {Θ : Levi k (fun _ : Fin 2 => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    ∃ hd : ∑ a, (x a).1 = 2, Nonempty ((parInd pts (ofChar Θ)).Equiv (prodIrr x hd)) := by
  obtain rfl := funext hx
  have key : ∀ g y, piTensor (fun a => detRep (Fin 1) (θ a)) g y = (Θ g : ℂ) • y := by
    intro g y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
    | smul_tprod c x =>
      rw [map_smul, smul_comm, piTensor_tprod, hΘ, Units.coe_prod]
      simp only [detRep, ofChar_apply, ← smul_eq_mul]
      rw [MultilinearMap.map_smul_univ]
      simp [detChar]
  let φ : (ofChar Θ).Equiv (piTensor fun a => detRep (Fin 1) (θ a)) :=
    .mk (PiTensorProduct.constantBaseRingEquiv (Fin 2) ℂ).toLinearEquiv.symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [key, ofChar_apply, ← smul_eq_mul, map_smul]
  exact ⟨rfl, ⟨(parIndEquiv pts φ).trans (multiProdEquiv pts fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a)))⟩⟩

end ProjLine

open ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}

end GlobalTheory.LocGL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar =====
