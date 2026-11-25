module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LieCharpolyRootPairs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

noncomputable section

namespace GlobalTheory.DetCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit

section Linear

variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

end Linear

variable {S : Scheme.{0}} {k : Type} [Field k]

variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem mem_lie_iff (t : Sp k ⟶ S) (v : epsPt t ⟶ G) :
    v ∈ Lie G t ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left :=
  ⟨fun h => congrArg (fun φ => φ.left) (show origin t ≫ v = 1 from h), fun h => Over.OverMorphism.ext h⟩

theorem isLieEigen_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen act t τ v ↔ ∃ h : v ∈ Lie G t, (⟨v, h⟩ : Lie G t) ∈ eigenspace act t τ :=
  ⟨fun h => ⟨(mem_lie_iff t v).2 h.1, fun a => Subtype.ext (Over.OverMorphism.ext (h.2 a))⟩,
    fun ⟨h, h'⟩ => ⟨(mem_lie_iff t v).1 h, fun a => congrArg (fun φ : Lie G t => φ.1.left) (h' a)⟩⟩

variable [IsCommMonObj G]

theorem comb_iff {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) (w : epsPt t ⟶ G) :
    (∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).1.left) ∧ w = (List.ofFn u).prod) ↔
      w = (comb v c).1 := by
  have key : (comb v c).1 = (List.ofFn fun i => (smulLie (c i) (v i)).1).prod := by
    rw [List.prod_ofFn]
    exact SubmonoidClass.coe_finsetProd (fun i => smulLie (c i) (v i)) Finset.univ
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain rfl : u = fun i => (smulLie (c i) (v i)).1 := funext fun i => Over.OverMorphism.ext (hu i)
    exact key.symm
  · rintro rfl
    exact ⟨fun i => (smulLie (c i) (v i)).1, fun _ => rfl, key⟩

def lieEquiv (t : Sp k ⟶ S) : Lie G t ≃ TanSp t G where
  toFun v := TanSp.mk v.1 (smT_zero_of t _ ((mem_lie_iff t _).1 v.2))
  invFun m := ⟨m.pt, (mem_lie_iff t _).2 (unit_of_smT_zero t _ m.tan)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lieEquiv_smul {t : Sp k ⟶ S} (c : k) (v : Lie G t) : lieEquiv t (smulLie c v) = c • lieEquiv t v := rfl

theorem lieEquiv_act (act : OAct O G) (t : Sp k ⟶ S) (a : O) (v : Lie G t) :
    lieEquiv t (actLie act t a v) = TanSp.act t act a (lieEquiv t v) := rfl

theorem lieEquiv_comb {t : Sp k ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) :
    lieEquiv t (comb v c) = ∑ i, c i • lieEquiv t (v i) := by
  apply TanSp.ext
  rw [TanSp.pt_sum]
  exact SubmonoidClass.coe_finsetProd (fun i => smulLie (c i) (v i)) Finset.univ

theorem mem_eigenspace_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (v : Lie G t) :
    v ∈ eigenspace act t τ ↔ lieEquiv t v ∈ eigenSub (TanSp.act t act) τ := by
  rw [mem_eigenSub]
  refine forall_congr' fun a => ?_
  rw [← lieEquiv_act, ← lieEquiv_smul, (lieEquiv t).injective.eq_iff]

theorem comb_mem {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by
  rw [mem_eigenspace_iff, lieEquiv_comb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((mem_eigenspace_iff act t τ _).1 (hv i))

theorem lieMult_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    LieMult act t τ n ↔ HasEigenDim act t τ n := by
  constructor
  · rintro ⟨v, hv, h⟩
    choose h1 h2 using fun i => (isLieEigen_iff act t τ _).1 (hv i)
    let v' : Fin n → Lie G t := fun i => ⟨v i, h1 i⟩
    have h' : ∀ w ∈ eigenspace act t τ, ∃! c, w = comb v' c := fun w hw => by
      have := h w.1 ((isLieEigen_iff act t τ _).2 ⟨w.2, hw⟩)
      exact (existsUnique_congr fun c => (comb_iff v' c w.1).trans Subtype.ext_iff.symm).1 this
    refine ⟨v', h2, fun c _ => comb_mem h2 c, fun c _ c' _ e => (h' _ (comb_mem h2 c)).unique rfl e,
      fun w hw => ?_⟩
    obtain ⟨c, hc, -⟩ := h' w hw
    exact ⟨c, trivial, hc.symm⟩
  · rintro ⟨v, hv, -, hi, hs⟩
    refine ⟨fun i => (v i).1, fun i => (isLieEigen_iff act t τ _).2 ⟨(v i).2, hv i⟩, fun w hw => ?_⟩
    obtain ⟨h1, h2⟩ := (isLieEigen_iff act t τ _).1 hw
    obtain ⟨c, -, hc⟩ := hs h2
    refine (existsUnique_congr fun c => comb_iff v c w).2 ⟨c, (congrArg Subtype.val hc).symm, fun c' hc' => ?_⟩
    exact hi trivial trivial ((Subtype.ext hc' : (⟨w, h1⟩ : Lie G t) = comb v c').symm.trans hc.symm)

variable {E : Type} [Field E] [NumberField E]

theorem bijective_restrict [CharZero k] :
    Function.Bijective fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
  refine ⟨fun φ ψ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => RingHom.congr_fun h a, fun τ => ?_⟩
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_splitting [CharZero k] [IsAlgClosed k] :
    ∃ _ : Fintype (𝓞 E →+* k), IsSplitting fun τ : 𝓞 E →+* k => τ := by
  classical
  let e := Equiv.ofBijective _ (bijective_restrict (E := E) (k := k))
  let F : Fintype (𝓞 E →+* k) := Fintype.ofEquiv _ e
  refine ⟨F, isSplitting_of_isDomain (σ := fun τ : 𝓞 E →+* k => τ) Function.injective_id ?_ (RingHom.id k) ?_⟩
  · rw [← NumberField.Embeddings.card E k]
    exact Fintype.card_congr e.symm
  · simpa using NumberField.discr_ne_zero E

variable [IsCMField E]

end GlobalTheory.DetCompare
