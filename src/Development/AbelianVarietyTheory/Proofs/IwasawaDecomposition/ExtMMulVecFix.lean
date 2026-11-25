module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section ExtL

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

theorem extM_mul_incl (g : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin N) (Fin n) A)
    (hM : ∀ b j, M b j = if b = Br.iC hN j then 1 else 0) : extM hN g * M = M * g := by
  subst hN
  ext b j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have e1 : ∑ l, extM rfl g b l * M l j = extM rfl g b (Br.iC rfl j) := by
    rw [Finset.sum_eq_single (Br.iC rfl j)]
    · simp [hM]
    · intro l _ hl
      simp [hM, hl]
    · simp
  rw [e1]
  refine Fin.lastCases ?_ (fun i => ?_) b
  · have h3 : ∀ l : Fin n, Fin.last n ≠ Br.iC (rfl : n + 1 = n + 1) l := fun l => (Fin.castSucc_lt_last l).ne'
    simp only [hM, h3, ite_false, zero_mul, Finset.sum_const_zero]
    exact extM_last_castSucc g j
  · have h3 : ∀ l : Fin n, (i.castSucc = Br.iC (rfl : n + 1 = n + 1) l) ↔ i = l := fun l => Fin.castSucc_inj
    simp only [hM, h3]
    simp
    exact extM_castSucc g i j

theorem extM_mulVec_fix (g : Matrix (Fin n) (Fin n) A) (z : Fin N → A) (hz : ∀ b, b ≠ Br.iL hN → z b = 0) :
    extM hN g *ᵥ z = z := by
  funext b
  by_cases e : b = Br.iL hN
  · subst e
    rw [extM_mulVec_iL]
  · have hb : b.1 < n := by
      have h3 := b.2
      have h4 : b.1 ≠ n := fun h => e (Fin.ext h)
      omega
    have e2 : b = Br.iC hN ⟨b.1, hb⟩ := Fin.ext rfl
    rw [e2, extM_mulVec_iC]
    have : iniH hN z = 0 := by
      funext i
      refine hz _ fun h => ?_
      have := congrArg Fin.val h
      exact absurd this (Nat.ne_of_lt i.2)
    rw [this, Matrix.mulVec_zero]
    exact (hz _ (by rw [← e2]; exact e)).symm

theorem eq_extM_of_laws (g : Matrix (Fin n) (Fin n) A) (G : Matrix (Fin N) (Fin N) A)
    (h1 : ∀ x, iniH hN (G *ᵥ x) = g *ᵥ iniH hN x) (h2 : ∀ x, (G *ᵥ x) (Br.iL hN) = x (Br.iL hN)) : G = extM hN g := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext b
  by_cases e : b = Br.iL hN
  · subst e
    rw [h2, extM_mulVec_iL]
  · have hb : b.1 < n := by
      have h3 := b.2
      have h4 : b.1 ≠ n := fun h => e (Fin.ext h)
      omega
    have e2 : b = Br.iC hN ⟨b.1, hb⟩ := Fin.ext rfl
    rw [e2, extM_mulVec_iC]
    exact congrFun (h1 _) _

end ExtL

theorem exists_ka_tw (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k) (c : (I.stX a).Cl) {y' : GA B (B.R.N B.R.m - 1)}
    (hp : PtOf (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c)))
      (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1)) :
    ∃ κ : U (chOf ((I.perIn u a).tilC c)),
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) *
          y ((I.perIn u a).tilC c) = extGL (N_m_succ B.R) y' * κ.1 ∧
      (((chi _ κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr _
        ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : B.LLˣ) : B.LL) := by
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm ⊢
  have hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c)))) _ := isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹
  let κ0 : (I.stp u a B.R.m).G (I.perIn u a).b0 := (1, m.2.1, m.2.2)
  have hgam : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m))
  have hempty : ∀ p : (I.stp u a B.R.m).D (I.perIn u a).b0, p.1.2 = ∅ := fun p => by
    have h := p.2
    rw [congrArg (fun y => y.ys p.1.1.deco.1.N) (ysAt_m B.R I.sel (I.tup a) (I.cst a))] at h
    exact h
  have hact : ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG (E := B.fields.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) •
        (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1) := by
    have e1 : FrmG.incl _ _ m • ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1 =
        tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1) hm
    rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m (I.perIn u a).b0)
        (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m (I.perIn u a).b0) κ0 =
        (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG (E := B.fields.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) *
        FrmG.incl _ _ m := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1) e2
  have hcos : cosetIn ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))) =
      cosetIn ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) := by
    ext z
    simp [cosetIn, hempty]
  obtain ⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y ((I.perIn u a).tilC c))⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * extGL (N_m_succ B.R) y' := ⟨_, rfl⟩
  have hxk : y ((I.perIn u a).tilC c) * x * k (chOf ((I.perIn u a).tilC c)) = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c))) := by
    rw [hx]; group
  have hq : PtOf (y ((I.perIn u a).tilC c) * x * k (chOf ((I.perIn u a).tilC c))) ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    rw [hxk, hact]
    exact hp'
  have hxU : x ∈ U (chOf ((I.perIn u a).tilC c)) := (hR.lev ((I.perIn u a).tilC c) x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩
  have hchr := hR.chr ((I.perIn u a).tilC c) ⟨x, hxU⟩ κ0 hgam hq
  refine ⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩
  · have e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam (I.perIn u a).b0 m))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    show _ = extGL (N_m_succ B.R) y' * x⁻¹
    rw [hx, e]
    group
  · rw [map_inv, inv_inv]
    exact hchr

theorem til_tw (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {l0 : I.Law0 l} {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {J : Formalism.L2.Herm.TwChJointS T H}
    {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}
    (hF : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hW : I.StdW l Z l0 W) (hLv : I.StdLv l Z l0 Lv)
    (u : B.Word) (a : I.ι) (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m)
    (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) (T.Q a)))
    (hK : I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat fun c s => (K.stabI c s).1)
    {k : T.Ch u a B.R.m → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) :
    ∃ Tl : SymmetricTwistedTiltedData Lv u a ha h1 K, Tl.z0 = TC.z0 X u ∧
      ∀ (φ : (I.chain l u a).cls B.R.m → (I.chain l u a).Y B.R.m → ℂ) c s s',
        IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Tl.ga c).1.1) (twYS T F u a B.R.m le_rfl s') (twYS T F u a B.R.m le_rfl s) →
        (I.per l u a).evz φ c s =
          ((((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m ((I.fm l u a).til c))).lev.chi (Tl.ka c))⁻¹ : ℂˣ) : ℂ) *
            φ ((I.fm l u a).til c) s' := by
  obtain ⟨-, -, hiX, hsp⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hg, -, -⟩ := hsp B.R.m le_rfl
  have hN := N_m_succ B.R
  have hga : ∀ c, (I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) := by
    intro c
    rw [hg]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u a).step B.R.m).unit _ _
  have hext : ∀ (R' : Type) [CommRing R'] (φ : (I.rec7 l Z).host.E →+* R') (g' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) R'),
      IsExt (I.rec7 l Z) (z0 X u) φ g' (extM hN g') := by
    intro R' _ φ g'
    refine ⟨extM_mul_incl hN g' _ fun b j => ?_, extM_mulVec_fix hN g' _ fun b hb => ?_⟩
    · refine (congrArg φ (TilX.iXm_apply hiX hN b j)).trans ?_
      by_cases h : b = Br.iC hN j
      · rw [ite_eq_left h]
        exact (congrArg φ (ite_eq_left h)).trans φ.map_one
      · rw [ite_eq_right h]
        exact (congrArg φ (ite_eq_right h)).trans φ.map_zero
    · show φ (TC.z0 X u b) = 0
      have e : TC.z0 X u = z0v B X u := rfl
      rw [e, lastCoordinateUniformizerVector_eq_single, Pi.single_eq_of_ne hb]
      exact φ.map_zero
  have hka := fun c => exists_ka_tw I u a hR c (y' := (K.y c).1)
    (hT _ _ _ _ (hK.pt c) (hext _ _ _))
  choose ka _ hka2 using hka
  let Tl : SymmetricTwistedTiltedData Lv u a ha h1 K :=
    { z0 := z0v B X u
      ga := fun c => ⟨_, hga c⟩
      ka := ka }
  refine ⟨Tl, rfl, ?_⟩
  intro φ c s s' hs
  have hyS : ∀ s, (twYS T F u a B.R.m le_rfl s).1 = s.1 := fun s => by
    have e := congrArg (fun f => Equiv.symm f s) (hW.eY u a B.R.m le_rfl)
    refine (congrArg (fun y => (eYS (F u) B.R.m le_rfl y).1) e).trans ?_
    show (eYS (F u) B.R.m le_rfl s).1 = s.1
    rw [eYS_end (F u) B.R.m le_rfl (Or.inr rfl)]
    exact (hF u).1.eY _ _ (Or.inr rfl) s
  have hy1 := hyS s
  have hy2 := hyS s'
  have hemb : ∀ τ, Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Tl.ga c).1.1 τ =
      (((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1).map (embAt B.embLL B.fields.emb τ) := fun τ =>
    congrArg (fun f : B.host.E →+* ℂ => ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1.map f) (B.fields_embC τ).symm
  have e1 := TilX.frMul_inv_eq B.fields.emb B.embLL ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) s s'
    (fun τ => (congrFun hy1 τ).symm.trans ((hs τ).trans (congrArg₂ (· * ·) (hemb τ) (congrFun hy2 τ))))
  have e2 := trFr_apply B.fields.emb B.embLL ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))
    ((I.stp u a B.R.m).chr _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) (φ ((I.perIn u a).tilC c)) s
  rw [e1, ← hka2 c] at e2
  exact e2

end GlobalTheory.Mem.Col2.TwP

end
