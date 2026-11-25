module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Guard

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

alias sp_comp := _root_.GlobalTheory.spMap_comp_ring

end Lat

section Norm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Comb

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}

theorem exists_comb (hu : ∀ k, IsTanAtG t x (u k)) (cf : Fin m → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun _ => smT_zero_ovT _) cf),
    (isCombAtG_iff t x (fun j => ovT (hu j)) cf _).2 rfl⟩

theorem comb_unique (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h')

theorem comb_tan (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb hu cf
  exact comb_unique hu h2 h ▸ h1

theorem comb_smul (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (a : R) : IsCombAtG t x u (fun k => a * cf k) (spMap (epsMul a) ≫ w) := by
  rw [← (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h]
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 (by rw [← smT_combT]; rfl)


variable (t x u) in
def Indep : Prop := ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

theorem indep_iff {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ k, IsTanAtG t x (v k))
    (hi : Indep t x v) (A : Matrix (Fin n) (Fin m) R) (hA : ∀ i, IsCombAtG t x v (fun j => A j i) (u i)) :
    Indep t x u ↔ Function.Injective A.mulVec := by
  have hu := fun i => comb_tan hv (hA i)
  refine ⟨fun h cf cf' e => ?_, fun h cf cf' w h1 h2 => h (hi _ _ w (tanLinG v hv u A cf w hA h1)
    (tanLinG v hv u A cf' w hA h2))⟩
  obtain ⟨w, -, h1⟩ := exists_comb hu cf
  obtain ⟨w', -, h2⟩ := exists_comb hu cf'
  have h3 := comb_unique hv (tanLinG v hv u A cf w hA h1) (e ▸ tanLinG v hv u A cf' w' hA h2)
  exact h cf cf' w h1 (h3 ▸ h2)

theorem indep_of_basis (hu : ∀ k, IsTanAtG t x (u k))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x u cf w) : Indep t x u :=
  fun _ _ w h1 h2 => (hb w (comb_tan hu h1)).unique h1 h2

end Comb

theorem exists_left_inv {K : Type} [Field K] {n m : ℕ} (A : Matrix (Fin n) (Fin m) K) (h : Function.Injective A.mulVec) :
    ∃ B : Matrix (Fin m) (Fin n) K, B * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

variable {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X} {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

theorem tri_mulVec {K : Type} [Field K] {A : Matrix (Fin m) (Fin m) K} (hA : A.BlockTriangular id) {i : Fin m}
    {cf : Fin m → K} (h : ∀ k, i < k → cf k = 0) :
    (∀ k, i < k → A.mulVec cf k = 0) ∧ A.mulVec cf i = A i i * cf i := by
  have e : ∀ k, A.mulVec cf k = ∑ j, A k j * cf j := fun _ => rfl
  simp only [e]
  refine ⟨fun k hk => Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)⟩
  · rcases le_or_gt j i with hj | hj
    · rw [hA (show id j < id k from hj.trans_lt hk), zero_mul]
    · rw [h j hj, mul_zero]
  · rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hA (show id j < id i from hj), zero_mul]
    · rw [h j hj, mul_zero]

end Norm

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section AnyBase

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]

variable {Z Ω}
end AnyBase

end Pts

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end GlobalTheory.ShFam.Pad.Guard
