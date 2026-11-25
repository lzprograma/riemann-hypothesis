module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory

namespace SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IrreducibleAdmissible : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π

def JacquetFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsSmooth π → HasFiniteLength π → HasFiniteLength (jac e π)

def InductionFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd e ρ)

def InductionContragredient : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → ∃ Φ : (parInd e (contra ρ)).Equiv (contra (parInd e ρ)),
      ∀ (f' : IndSp e (contra ρ)) (f : IndSp e ρ),
        (Φ f' : Module.Dual ℂ (IndSp e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ

end SmGL

namespace Published

def BernsteinZelevinskyFiniteness : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    IrreducibleAdmissible k ∧ JacquetFiniteLength k ∧ InductionFiniteLength k ∧
      InductionContragredient k

end Published

namespace SmGL

section Transport

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]

theorem hasFiniteLength_iff_wellFounded (ρ : Representation F G V) :
    HasFiniteLength ρ ↔
      WellFoundedGT (Subrepresentation ρ) ∧ WellFoundedLT (Subrepresentation ρ) := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', isArtinian_iff]
  refine and_congr ⟨fun _ => φ.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.symm.toOrderEmbedding.wellFoundedGT⟩ ⟨fun h => ?_, fun _ => ?_⟩
  · haveI : WellFoundedLT (Submodule (MonoidAlgebra F G) ρ.asModule) := h
    exact φ.toOrderEmbedding.wellFoundedLT
  · exact φ.symm.toOrderEmbedding.wellFoundedLT

theorem hasFiniteLength_comp_iff (ρ : Representation F G V) (s : H →* G) (hs : Function.Surjective s) :
    HasFiniteLength (ρ.comp s : Representation F H V) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (ρ.comp s : Representation F H V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨h, rfl⟩ := hs g
        exact S.apply_mem_toSubmodule h hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (s h) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_isIrreducible {ρ : Representation F G V} (h : ρ.IsIrreducible) :
    HasFiniteLength ρ := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  haveI : Finite (Subrepresentation ρ) := IsSimpleOrder.instFinite
  exact (hasFiniteLength_iff_wellFounded ρ).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_smInd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P : Subgroup G} {σ : Representation ℂ P W} (f : smoothPart (ind P σ)) :
    IsLocallyConstant (f.1.1 : G → W) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : {g : G | ind P σ g f.1 = f.1} ∈ nhds ((fun y => x⁻¹ * y) x) :=
    IsOpen.mem_nhds f.2 (by simp)
  filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
  have hy' : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
  rwa [mul_inv_cancel_left] at hy'

theorem InductionContragredient.nonempty_equiv (h : InductionContragredient k) (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) :
    Nonempty ((parInd e (contra ρ)).Equiv (contra (parInd e ρ))) := by
  haveI : LocallyCompactSpace (GL n k) := SplitFlip.locallyCompact_GL
  borelize (GL n k)
  obtain ⟨Φ, -⟩ := h _ _ _ e Measure.haar W ρ hρ
  exact ⟨Φ⟩

end SmGL

end GlobalTheory
