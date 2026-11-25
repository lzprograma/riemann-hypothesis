module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalRingCardinality.HostCls
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar

abbrev frobOrder (D : D7) (p : ℕ) : ℕ := orderOf (zH D.R.toFrame (hP D p))

theorem frobOrder_spec (D : D7) {T p : ℕ} (hg : GIdx D.host T p) : 2 ≤ frobOrder D p ∧ Even (frobOrder D p) := by
  obtain ⟨hp, -, hc, hn, -⟩ := hg
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hL⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -⟩ := D.host.der.frob p (not_dvd_conductor_of_inert hp hc) P
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hPp, hL, σ, hσ, rfl⟩
  obtain ⟨P', hP', hL', σ', hσ', heq⟩ := Classical.epsilon_spec hne
  have hnF : frobOrder D p = orderOf (D.R.iota (hP D p)) := by
    unfold frobOrder
    rw [← Subgroup.orderOf_coe]
    exact orderOf_injective (MonoidHom.inr Formalism.FrobeniusOrbits.G0 D.R.MA) (fun a b hab => (Prod.ext_iff.1 hab).2) _
  have hev : Even (orderOf (D.R.iota (hP D p))) := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← heq]
    exact @hn P' hP' hL' σ' hσ'
  have hpos : 0 < orderOf (D.R.iota (hP D p)) := orderOf_pos _
  rw [hnF]
  obtain ⟨k, hk⟩ := hev
  exact ⟨by omega, k, hk⟩

section Pack

variable (D : D7) (u : D.what₂.Word)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
  (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ frobOrder D (D.what₂.places.resChar w))
  (he : Even (frobOrder D (D.what₂.places.resChar w)))
  (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
    (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
    (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def pack : LocPack D u Lc (D.what₂.places.resChar w) where
  W := WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  Qq := QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  O := ORec D w (frobOrder D (D.what₂.places.resChar w))
  Kf := KfRec D w (frobOrder D (D.what₂.places.resChar w))
  ι := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp
    (iota (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  σ := sig (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  j := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ.comp
    (jO (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  w := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ
    (wU (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  hS := by
    let p := D.what₂.places.resChar w
    let n := frobOrder D p
    have h := (settingStd p n h5 h2 he).1
    let X := extRec D w n
    exact
      { prime := h.prime
        five_le := h.five_le
        two_le := h.two_le
        even := h.even
        frac_alt := h.frac_alt
        frac_O := X.frac
        p_unif := h.p_unif
        res_card := h.res_card
        eq_sum_herm_smul_frame_of_inW := h.eq_sum_herm_smul_frame_of_inW
        frob := h.frob
        period := h.period
        ι_comp := by
          intro x
          change X.φK (iota p n (algebraMap (WQ p n) (QQ p n) x)) = _
          rw [h.ι_comp, X.comm]
          rfl
        finite := X.fin.comp h.finite
        complete_O := X.complete
        w_sq := by
          change X.φ (wU p n) ^ 2 = (p : ORec D w n)
          rw [← map_pow, h.w_sq, map_natCast] }
  I := I
  ψ := ψ

end Pack

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def packAll : ∀ u (w : D.what₂.places.Pl) (_h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LocPack D u (Lc u) (D.what₂.places.resChar w) :=
  fun u w h => pack D u (Lc u) w h.2.1 (frobOrder_spec D h).1 (frobOrder_spec D h).2 (I u w h) (ψ u w h)

variable (hd : ∀ u w h, ((packAll D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev record : D7 := recG D sc Ce Lc (packAll D Lc I ψ) hd

end Record

end GlobalTheory.Mem.LocalPack
