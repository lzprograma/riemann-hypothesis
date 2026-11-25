module

import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwistInputsTest

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def act (i : X.Tw) (j : ℕ) (b : Bool) :=
  MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))

theorem act_single (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    act Y i j b (MonoidAlgebra.single g 1) x = Y.actG i j b g x := by
  simp [act]

theorem eG_on_irred (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GIrred Y i j b W) : (∀ x ∈ W, eG Y i j b x = x) ∨ (∀ x ∈ W, eG Y i j b x = 0) := by
  apply Formalism.MainNotions.IntegralHeckeForms.eG_irred <;> assumption

theorem act_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g x, Y.actG i j b g (T x) = T (Y.actG i j b g x))
    (z : MonoidAlgebra (FractionRing (X.O i)) (G0g N)) (x : Y.Fm i j b) :
    act Y i j b z (T x) = T (act Y i j b z x) := by
  induction z using MonoidAlgebra.induction_on with
  | of g => simpa [act] using hT g x
  | add f g hf hg => simp only [map_add (f := _), LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem eG_actG (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    eG Y i j b (Y.actG i j b g x) = Y.actG i j b g (eG Y i j b x) := by
  have he : eG Y i j b = act Y i j b (Y.eAlg i b) := rfl
  rw [he, ← act_single, ← act_single, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    Y.eAlg_central]

theorem mem_typeSubspace_iff_unipotent_character (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : x ∈ Fm0 Y i j b ↔ ∀ u : Y.U,
    Y.actG i j b u x = ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  simp [Fm0, Submodule.mem_iInf, sub_eq_zero]

theorem goodPart_le_typeSubspace (i : X.Tw) (j : ℕ) (b : Bool) : V0 Y i j b ≤ Fm0 Y i j b := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_typeSubspace_iff_unipotent_character]
  intro u
  rw [← eG_actG, (mem_typeSubspace_iff_unipotent_character Y i j b x).1 hx u, map_smul]

theorem twOK_of_psiOk (i : X.Tw) (A Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A Q k' ψ') (b : Bool) :
    TwOK i k' Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) ∧
      UnrG (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ'.comp (X.art i Q))) ∧ Disjoint Q A := by
  classical
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ := h
  rw [Finset.disjoint_union_right] at h2
  set ψ := ψ'.comp (X.art i Q)
  have hu : UnrG ψ := by
    intro k v hv A' hA σ hσ
    by_contra hne
    have hQ : v ∈ (Q : Set (PlE D.host)) := (h7 v A' hA).1 ⟨σ, hσ, hne⟩
    exact Finset.disjoint_left.1 h2.1 hQ (X.placesOver_subset_exceptional i k hv)
  cases b
  · have hk : (ψ⁻¹).ker = ψ.ker := by ext g; simp [MonoidHom.mem_ker]
    refine ⟨⟨fun P hP => (h1 P hP).1, h2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_, h2.2⟩
    · show IsOpen (((ψ⁻¹).ker : Subgroup (G D.host.E N.Om)) : Set (G D.host.E N.Om)); rw [hk]; exact h4
    · intro g g' hg; show (ψ g')⁻¹ = ((ψ g)⁻¹)⁻¹; rw [h5 g g' hg]
    · intro g; exact Subgroup.inv_mem _ (h6 g)
    · intro v A' hA
      rw [← h7 v A' hA]
      exact exists_congr fun σ => and_congr_right fun _ => inv_ne_one
    · intro v hv A' hA σ hσ; exact inv_eq_one.2 (h8 v hv A' hA σ hσ)
    · intro k v hv A' hA σ hσ; exact inv_eq_one.2 (hu k v hv A' hA σ hσ)
  · exact ⟨⟨fun P hP => (h1 P hP).1, h2.1, h4, h5, h6, h7, h8⟩, hu, h2.2⟩

theorem admissibleGoodIdempotent_iff_reduced : GroupAlgebraIntegrality Y ↔ ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (b : Bool),
    (∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
        (Y.actG i j b g).toLinearMap ∘ₗ Y.hkF i j b k P = Y.hkF i j b k P ∘ₗ (Y.actG i j b g).toLinearMap :=
  ⟨fun h i hi b => ⟨(h i hi b).1, fun j hj => ((h i hi b).2 j hj).1⟩,
    fun h i hi b => ⟨(h i hi b).1, fun j hj => ⟨(h i hi b).2 j hj, fun _ W _ hW => eG_on_irred Y i j b W hW⟩⟩⟩

end GlobalTheory.TwistInputsTest

end
