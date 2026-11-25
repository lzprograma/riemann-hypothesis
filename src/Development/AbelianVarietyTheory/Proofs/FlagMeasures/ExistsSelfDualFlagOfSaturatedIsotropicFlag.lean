module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.FullFlag

theorem rkK_mono {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [FiniteDimensional K V] {M N : Submodule (𝓞 K) V} (h : M ≤ N) : Formalism.HN.rkK M ≤ Formalism.HN.rkK N :=
  Submodule.finrank_mono (Submodule.span_mono h)

theorem main : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  intro I xf a j S hS
  obtain ⟨h0, hmono, hrk, hsat, hiso⟩ := hS
  set x : I.GA := (1, xf) with hx
  obtain ⟨-, hA, -, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨-, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hmain⟩ := PerpStep.main I x
  have hform : ∀ s y : Fin I.n → I.E,
      star s ⬝ᵥ (I.J *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J s y := by
    intro s y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply,
      -star_trivial]
  have hmem : ∀ N y, y ∈ perpIn I x N ↔ y ∈ lamX I x ∧ ∀ s ∈ N, star s ⬝ᵥ (I.J *ᵥ y) = 0 := by
    intro N y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
    simp only [hform]
  have hsatS : ∀ i, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    have e : S i = lamX I x ⊓ (Submodule.span I.E (S i : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) := by
      ext y
      exact hsat i y
    rw [e]
    exact PerpStep.sat_inf (bas I) (frm I x) hX _ hA _
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      ∀ b, G b = S ⟨min b a, Nat.lt_succ_of_le (min_le_right _ _)⟩ := ⟨_, fun _ => rfl⟩
  have hGS : ∀ i : Fin (a + 1), G i = S i := by
    intro i
    rw [hG]
    congr 1
    ext
    have := i.2
    simp only
    omega
  have hG0 : G 0 = ⊥ := (hGS 0).trans h0
  have hGm : Monotone G := by
    intro b c h
    rw [hG, hG]
    exact hmono (Fin.mk_le_mk.2 (min_le_min_right _ h))
  have hGsat : ∀ b, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G b) := by
    intro b
    rw [hG]
    exact hsatS _
  have hGr : ∀ i : Fin a, Formalism.HN.rkK (G (i + 1)) = Formalism.HN.rkK (G i) + j i := by
    intro i
    have h1 := hGS i.succ
    have h2 := hGS i.castSucc
    rw [Fin.val_succ] at h1
    rw [Fin.val_castSucc] at h2
    rw [h1, h2, hrk]
  have hGsum : ∀ b (hb : b ≤ a), Formalism.HN.rkK (G b) = ∑ i : Fin b, j (Fin.castLE hb i) := by
    intro b
    induction b with
    | zero => intro _; simp [hG0, Formalism.HN.rkK]
    | succ b ih =>
      intro hb
      rw [Fin.sum_univ_castSucc]
      have := hGr ⟨b, hb⟩
      simp only at this
      rw [this, ih (by omega)]
      rfl
  have hGa : Formalism.HN.rkK (G a) = ∑ i, j i := by
    rw [hGsum a le_rfl]; rfl
  have hPr : ∀ b, Formalism.HN.rkK (perpIn I x (G b)) + Formalism.HN.rkK (G b) = I.n :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.1
  have hPP : ∀ b, perpIn I x (perpIn I x (G b)) = G b :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.2.1
  have hPa : ∀ b c, b ≤ c → perpIn I x (G c) ≤ perpIn I x (G b) :=
    fun b c h => (hmain _ _ (hGsat b) (hGsat c) (hGm h)).2.2.2.1
  have hP0 : perpIn I x (G 0) = lamX I x := by
    ext y
    rw [hmem, hG0]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp
  have hmid : G a ≤ perpIn I x (G a) := by
    intro y hy
    have e : G a = S (Fin.last a) := hGS (Fin.last a)
    rw [hmem]
    refine ⟨(hGsat a).1 hy, fun s hs => ?_⟩
    rw [hform]
    rw [e] at hs hy
    exact hiso s hs y hy
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ b, b ≤ a → F b = G b) ∧ ∀ b c, a < b → c = 2 * a + 1 - b → F b = perpIn I x (G c) :=
    ⟨fun b => if b ≤ a then G b else perpIn I x (G (2 * a + 1 - b)), fun b hb => ite_eq_left hb,
      fun b c hb hc => hc ▸ ite_eq_right (by omega)⟩
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun b => ?_
    rcases lt_trichotomy b a with h | rfl | h
    · rw [hF1 b h.le, hF1 (b + 1) h]
      exact hGm (by omega)
    · rw [hF1 b le_rfl, hF2 (b + 1) b (by omega) (by omega)]
      exact hmid
    · rw [hF2 b _ h rfl, hF2 (b + 1) _ (by omega) rfl]
      exact hPa _ _ (by omega)
  have hFtop : ∀ b, 2 * a + 1 ≤ b → F b = lamX I x := fun b hb => by
    rw [hF2 b 0 (by omega) (by omega), hP0]
  refine ⟨F, fun b => Formalism.HN.rkK (F (b + 1)) - Formalism.HN.rkK (F b), ⟨hFm, ?_, ?_, ?_⟩, hFtop _ le_rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF1 0 (by omega), hG0]
  · intro b hb
    rw [hFtop b hb, hFtop _ le_rfl]
  · intro b hb y
    rw [hFtop _ le_rfl, ← hmem]
    by_cases h : b ≤ a
    · rw [hF1 b h, hF2 _ b (by omega) (by omega)]
    · rw [hF2 b _ (by omega) rfl, hPP, hF1 _ (by omega)]
  · intro i
    rw [hF1 i (by have := i.2; omega), hGS]
  · intro b
    have := rkK_mono (hFm (Nat.le_succ b))
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega
  · intro i
    have hi := i.2
    have h1 := hGr i
    have h2 := hPr i
    have h3 := hPr (i + 1)
    simp only
    rw [hF1 i (by omega), hF1 (i + 1) (by omega), hF2 (2 * a - i + 1) i (by omega) (by omega),
      hF2 (2 * a - i) (i + 1) (by omega) (by omega)]
    omega
  · have h2 := hPr a
    simp only
    rw [hF1 a le_rfl, hF2 (a + 1) a (by omega) (by omega)]
    omega
  · intro b hb
    simp only
    rw [hFtop b hb, hFtop _ (by omega), Nat.sub_self]

end GlobalTheory.RadCov.FullFlag
