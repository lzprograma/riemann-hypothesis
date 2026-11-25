module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCover
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.NonzeroGenerates

alias spMap_comp' := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp

theorem spMap_id' {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) :=
  Spec.map_id (CommRingCat.of A)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S T U : Type} [CommRing S] [CommRing T] [CommRing U]

theorem eq_id_comp (x : Sp S ⟶ Xo.X) : x = spMap (RingHom.id S) ≫ x := by
  rw [spMap_id', Category.id_comp]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) : scal x (a * b) i = scal x a i * scal x b i :=
  ((_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 a b i).1

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 :=
  ((_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 1 1 i).2.2

theorem secBC_id_iff (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i :=
  (_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.1 a s t

theorem exists_mul (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) :
    ∃ t : LB.Sec (PPx x), ∀ i, t.f i = scal x a i * s.f i := by
  obtain ⟨t, ht, -⟩ := _root_.GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo S S (RingHom.id S) a x x (eq_id_comp x) s
  exact ⟨t, (secBC_id_iff x a s t).1 ht⟩

theorem exists_pull (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (hx : x' = spMap φ ≫ x)
    (s : LB.Sec (PPx x)) : ∃ s' : LB.Sec (PPx x'), SecBC φ 1 x x' s s' :=
  (_root_.GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo S T φ 1 x x' hx s).exists

theorem pull_trans_iff {φ : S →+* T} {ψ : T →+* U} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} {x'' : Sp U ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) (hx' : x'' = spMap ψ ≫ x') {a : S} {s s' s''} (h : SecBC φ a x x' s s') :
    SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'' :=
  (_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S T U φ ψ x x' x'' hx hx').1 a s s' s'' h

theorem pull_mul_iff {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') :
    SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i :=
  (_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S T T φ _ x x' x' hx (eq_id_comp x')).2.2.1 a s s' t' h

theorem pull_iff_of_mul {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s t : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (hst : ∀ i, t.f i = scal x a i * s.f i)
    (h : SecBC φ 1 x x' s s') : SecBC φ 1 x x' t t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i := by
  rw [pull_trans_iff (eq_id_comp x) hx ((secBC_id_iff x a s t).2 hst), RingHom.comp_id, pull_mul_iff hx h]

theorem not_mem_of_mem_basicOpen_scal (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) (q : Gx x)
    (hq : q ∈ (Gx x).basicOpen (scal x a i)) : a ∉ (Formalism.L2.PjFree.gxSnd x q).asIdeal := by
  have e : scal x a i = ((Formalism.L2.PjFree.gxSnd x).appLE ⊤ ((PPx x).U i) le_top).hom (toΓ S a) := rfl
  rw [e] at hq
  erw [Scheme.basicOpen_appLE] at hq
  have h2 := hq.2
  have e2 : (Sp S).basicOpen (toΓ S a) = PrimeSpectrum.basicOpen a :=
    basicOpen_eq_of_affine (R := CommRingCat.of S) a
  erw [e2] at h2
  exact h2

theorem secGen_of_secGen {x : Sp S ⟶ Xo.X} {θ s : LB.Sec (PPx x)} (hθ : SecGen x θ) (hs : SecNZ x s) :
    SecGen x s := by
  obtain ⟨a, ha, -⟩ := hθ s
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hn
    obtain ⟨q, i, hq, hqi⟩ := hs ⟨m, hm.isPrime⟩
    rw [ha i, Scheme.basicOpen_mul] at hqi
    have := not_mem_of_mem_basicOpen_scal x a i q hqi.1
    rw [hq] at this
    exact this ham
  obtain ⟨u, rfl⟩ := hu
  intro t
  obtain ⟨b, hb, hbu⟩ := hθ t
  refine ⟨b * ↑u⁻¹, fun i => ?_, fun c hc => ?_⟩
  · rw [hb i, ha i, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right]
  · have : c * u = b := hbu _ fun i => by rw [hc i, ha i, ← _root_.mul_assoc, ← scal_mul]
    rw [← this, Units.mul_inv_cancel_right]

theorem secNZ_pull {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') (hs : SecNZ x s) : SecNZ x' s' :=
  fun p' => (_root_.GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S T φ x x' hx s s' h p').2 (hs _)

end GlobalTheory.Frames.NonzeroGenerates


open GlobalTheory.Frames.NonzeroGenerates in
theorem GlobalTheory.Frames.secGen_of_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecNZ x s → SecGen x s := by
  intros
  apply GlobalTheory.FrameGenerator.secGen_of_secNZ <;> assumption
