module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad, Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVChain\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCrd\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB CapInv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_capInv {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq) (hm : P.r ≤ B.opOrder Θ) :
    ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) := by
  have key : ∀ (G : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) F → ∀ p, Bs.inSS p →
        ∀ g ∈ GV P.k P.r, G (rho Bs p F) g = rho Bs p (G F) g) →
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = G F g) →
        B.Commutes Bs (B.GPos Bs) Θ := by
    intro G hG hA p hp f hf g hg
    have hgG : g ∈ GV P.k P.r := hg.1
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV P.k P.r := gv_mul (gv_inv h1.1) (gv_inv h2.1)
    have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV P.k P.r := gv_mul h4.1 h3.1
    have hck : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (x : B.Mat P.k P.r), x ∈ GV P.k P.r →
        CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) F → CkOn (B.opOrder Θ : ℕ∞) {x} F := by
      intro F x hx hF g₀ hg₀
      rw [Set.mem_singleton_iff] at hg₀
      subst hg₀
      exact hF _ hx
    have hfr : CkOn ((P.r : ℕ) : ℕ∞) (GV P.k P.r) f := sCkOn_mono (by exact_mod_cast hm) hf
    have hrho : CkOn (B.opOrder Θ : ℕ∞) (GV P.k P.r) (rho Bs p f) := by
      rw [rho_eq_trn']; exact CkOn_trn _ ha hb hf
    have hx : sgs p g ∈ GV P.k P.r := by
      rw [show sgs p g = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) by
        simp [sgs, Matrix.mul_assoc]]
      exact gv_mul (gv_mul ha hgG) hb
    rw [hA _ g hgG (hck _ g hgG hrho), hG f hfr p ⟨h1, h2, h3, h4⟩ g hgG]
    simp only [rho]
    rw [hA f (sgs p g) hx (hck f _ hx hf)]
  constructor
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF (Q.uC P.k P.r 0 y) 0 hp hg).1
  · exact key _ fun F hF p hp g hg =>
      (rho_AA_ck Bs hF 0 (y - ((2 * P.r + P.k : ℕ) : ℂ) / 2) hp hg).2

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_toda {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
      dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g := by
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rdsag_tvGrp {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c := by
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  set D := OmPlus P.k P.r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  let k := P.k
  let r := P.r
  let E := Wq →L[ℂ] Wp
  let TorV (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
    Algebra.adjoin ℂ {x | ∃ l : Fin r, l.val < j ∧ x = EA hD (esI k r l) (esI k r l)}

  have root_action_on_truncated_vector (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleEv)
      {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : b.val < a.val) :
      ((EA hD (esI k r a) (esI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
        (if a.val = b.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
    first
    | exact _root_.Formalism.FourierDecayAlt.P.CutMP.TVG.root_action_on_truncated_vector
    | apply _root_.Formalism.FourierDecayAlt.P.CutMP.TVG.root_action_on_truncated_vector <;> assumption

  have claimV (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion)
      (hD : IsOpen D) (v₀ : VS k r 0 D E) (g₀ : Mx k r) (w : ℂ)
      (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
      (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
      {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
      (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
      (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D) :
      ∀ (m : ℕ), m ≤ r → ∀ P ∈ TorV hD (r - m), ∀ c ∈ OmX r,
        La hD v₀ (wCell k r (Fin.last r) c * g₀) (qminor (EA hD) (colsVm k r m) (colsVm k r m) w * P) =
          kvC r w m (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) P) c := by
    exact _root_.Formalism.FourierDecayAlt.P.CutMP.TVG.claimV hRR hLR hTC hCh hD v₀ g₀ w z z' hz hz'
      hN (f := f) hf hLf hRf hv hg₀ hcell
  have h1N : (1 : Mx P.k P.r) ∈ Nlev P.k P.r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds P.k P.r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev P.k P.r 0 ∩ D, ∀ n ∈ Nlev P.k P.r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := P.k) (r := P.r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS P.k P.r 0 D (Wq →L[ℂ] Wp) := ⟨cut P.k P.r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs (c, g) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ Glev P.k P.r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hcl := claimV mirror_right_rule_holds mirror_left_rule_cell_holds mirror_torus_cell_holds mirror_chain_expansion_holds hD v₀ g
    (kvTop P.k P.r y) Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hg hcell P.r le_rfl 1 (Subalgebra.one_mem _) c hc
  rw [mul_one] at hcl
  have eR : kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (wCell P.k P.r (Fin.last P.r) c' * g)) c =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => La hD v₀ (wCell P.k P.r (Fin.last P.r) c' * g) 1) c :=
    kvC_loc _ _ _ _ (fun c' hc' => (cut_of_mem _ (hcell c' hc')).symm) hc
  rw [eR, ← hcl, La_apply]
  have hγ := hcell c hc
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y) :
      SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS P.k P.r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
        (kvTop P.k P.r y) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL P.k P.r 0 ∘ (cI ∘ colsVm P.k P.r P.r) = colsVm P.k P.r P.r := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
    (kvTop P.k P.r y)).loc (cut P.k P.r 0 D J) J (fun x' hx' => cut_of_mem _ hx') _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P.CutMP.TVG

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open scoped ContDiff in
theorem rdsag_todaV {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (y : ℂ) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (g : Q.Mx P.k P.r) (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) :
    Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g := by
  have e1 : capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
      drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)
    exact TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y
  have e2 := TVG.rdsag_tvGrp P Bs y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp hemb.contDiffOn (fun c' (hc' : c' ∈ U') => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := toda_coordinate_holds P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, ite_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_group_action : RDSAGrp := by
  intro Wp Wq _ _ _ _ _ _ P D hPl y
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := CutMP.capelli_representation_holds P.k P.r Wp Wq y
  refine ⟨Θ, Θv, ⟨_, _, hP⟩, ⟨_, _, hPv⟩, (CutMP.rdsag_capInv P D y Θ hO.ge).1 hA,
    (CutMP.rdsag_capInv P D y Θv hOv.ge).2 hAv, fun J hJ x hx => ?_⟩
  have hJB : J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (CutMP.Gauge.OmB D) := by
    rw [CutMP.JDAToda.omB_eq, ← ffl_om_eq]; exact hJ
  have hcell : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ CutMP.Gauge.OmB D := by
    rw [CutMP.JDAToda.omB_eq]
    have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq D x hx).1
    exact ⟨fun l _ => h.2.2 l (by simp), h.2.1⟩
  obtain ⟨hc, hg, -⟩ := hx
  constructor
  · obtain ⟨hGV, hCk⟩ := CutMP.capa_J_ck P D hJB hc hg hcell (B.opOrder Θ)
    rw [← CutMP.rdsag_toda P D y J hJB x.1 hc x.2 hg hcell]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := CutMP.capa_J_ck P D hJB hc hg hcell (B.opOrder Θv)
    rw [← CutMP.rdsag_todaV P D y J hJB x.1 hc x.2 hg hcell]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end Formalism.FourierDecayAlt.P.CutSE
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants

section loc

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rds_vABm_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (CutMP.vABm r Y i).1 f₁ c = (CutMP.vABm r Y i).1 f₂ c ∧
      (CutMP.vABm r Y i).2 f₁ c = (CutMP.vABm r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := rds_vABm_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [CutMP.vABm, dite_eq_left hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.smul_apply, cbOp]
        rw [(ih c hc).1, (ih c hc).2, _root_.Formalism.FourierDecayAlt.P.CutMP.TVG.pbOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [cbiOp]
        rw [(ih c hc).1]
    · simp only [CutMP.vABm, dite_eq_right hi]
      exact ih c hc

end loc

theorem spectral_action_locality : RDSALoc := by
  intro r E _ _ y f f' h c hc
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hpO : ∀ (l : Fin r) (g₁ g₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      pOp l g₁ c = pOp l g₂ c := by
    intro l g₁ g₂ hg c hc
    have hev : g₁ =ᶠ[nhds c] g₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) hg
    unfold pOp Formalism.QuantumDeterminants.wirt
    rw [ite_eq_left hc, ite_eq_left hc, hev.fderiv_eq]
  have hA : ∀ i : ℕ, ∀ g₁ g₂ : (Fin r → ℂ) → E, (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c ∧ (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := by
    intro i
    induction i with
    | zero =>
      intro g₁ g₂ hg c hc
      simp only [Q.vAB]
      exact ⟨hg c hc, by trivial⟩
    | succ i ih =>
      intro g₁ g₂ hg c hc
      have ih1 : ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).1
      have ih2 : ∀ c ∈ OmX r, (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).2
      simp only [Q.vAB]
      split_ifs with hi
      · refine ⟨?_, ?_⟩
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          rw [ih1 c hc, hpO ⟨i, hi⟩ _ _ ih1 c hc]
          simp only [cOp]
          rw [ih2 c hc]
        · simp only [ciOp]
          rw [ih1 c hc]
      · exact ih g₁ g₂ hg c hc
  exact ⟨(hA r f f' h c hc).1, (rds_vABm_loc y r f f' h c hc).1⟩

end Formalism.FourierDecayAlt.P.CutSE
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section pre

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r)

def rdsVp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tl Y l).prod

def rdsVvp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem rdsVp_zero (Y : ℂ) : rdsVp L Y 0 = 1 := by simp [rdsVp]

theorem rdsVvp_zero (Y : ℂ) : rdsVvp L Y 0 = 1 := by simp [rdsVvp]

theorem rdsVp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVp L Y (i + 1) = L.Tl Y ⟨i, h⟩ * rdsVp L Y i := by
  simp [rdsVp, List.take_add_one, h]

theorem rdsVvp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVvp L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * rdsVvp L Y i := by
  simp [rdsVvp, List.take_add_one, h]

theorem rds_tprod (Y : ℂ) : L.Tprod Y = rdsVp L Y r := by
  simp [R.LevelData.Tprod, rdsVp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem rds_tvprod (Y : ℂ) : L.Tvprod Y = rdsVvp L Y r := by
  simp [R.LevelData.Tvprod, rdsVvp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem rds_Tl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 0 0 = (algebraMap ℂ A Y + L.p l) * V 0 0 + -L.c l * V 1 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 1 0 = L.ci l * V 0 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tvl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ A Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tvl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

end pre

section rad

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rdsR_fst_neg (a : Pr V) : (-a).1 = -a.1 := rfl
theorem rdsR_fst_sub (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdsR_fst_one : (1 : Pr V).1 = 1 := rfl
theorem rdsR_fst_zero : (0 : Pr V).1 = 0 := rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)

theorem rds_op_coe (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.op l i Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn k r (Wq →L[ℂ] Wp)) :=
  X.op_apply l i Φ

theorem rds_vab_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.p ⟨i, h⟩).1 = X.op ⟨i, h⟩ 0 := by rw [hL.1 ⟨i, h⟩]; rfl
    have hc : (L.c ⟨i, h⟩).1 = X.op ⟨i, h⟩ 1 := by rw [hL.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.ci ⟨i, h⟩).1 = X.op ⟨i, h⟩ 2 := by rw [hL.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVp_succ L Y i h, rds_Tl_mul_0, rds_Tl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y + L.p ⟨i, h⟩) * rdsVp L Y i 0 0 +
          -L.c ⟨i, h⟩ * rdsVp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVp L Y i 0 0).1 Φ) + X.op ⟨i, h⟩ 0 ((rdsVp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 1 ((rdsVp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, rds_fst_add, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_algebraMap, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
          sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dite_eq_left h, ite_true, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rfl
    · have e : ((L.ci ⟨i, h⟩ * rdsVp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 2 ((rdsVp L Y i 0 0).1 Φ) := by
        rw [_root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dite_eq_left h]
      rfl

theorem rds_vabm_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVvp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVvp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVvp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.pb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 3 := by rw [hL.2.1 ⟨i, h⟩]; rfl
    have hc : (L.cb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 4 := by rw [hL.2.2.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.cbi ⟨i, h⟩).1 = X.op ⟨i, h⟩ 5 := by rw [hL.2.2.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVvp_succ L Y i h, rds_Tvl_mul_0, rds_Tvl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y - L.pb ⟨i, h⟩) * rdsVvp L Y i 0 0 +
          -L.cb ⟨i, h⟩ * rdsVvp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVvp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 3 ((rdsVvp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 4 ((rdsVvp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, rdsR_fst_sub, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_algebraMap, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply,
          Module.algebraMap_end_apply, sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dite_eq_left h, ite_true, Pi.sub_apply, Pi.smul_apply]
      rfl
    · have e : ((L.cbi ⟨i, h⟩ * rdsVvp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 5 ((rdsVvp L Y i 0 0).1 Φ) := by
        rw [_root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dite_eq_left h]
      rfl

theorem rds_cprod (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Φ : RadSp k r z z' π π'),
    ((((ls.map L.c).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => c l).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∧
      ((((ls.map L.cb).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => star (c l)).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro ls
  induction ls with
  | nil =>
    intro Φ
    refine ⟨?_, ?_⟩ <;> (funext c g; simp only [List.map_nil, List.prod_nil, one_smul]; rfl)
  | cons a ls ih =>
    intro Φ
    obtain ⟨h1, h2⟩ := ih Φ
    have hc : (L.c a).1 = X.op a 1 := by rw [hL.2.2.1 a]; rfl
    have hcb : (L.cb a).1 = X.op a 4 := by rw [hL.2.2.2.2.1 a]; rfl
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, hc, Module.End.mul_apply, rds_op_coe, h1]
      funext c g
      simp only [crd, opL, cOp, List.map_cons, List.prod_cons, smul_smul]
    · rw [List.map_cons, List.prod_cons, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, hcb, Module.End.mul_apply, rds_op_coe, h2]
      funext c g
      simp only [crd, opL, cbOp, List.map_cons, List.prod_cons, smul_smul]

end rad

theorem spectral_radial_action : RDSARad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X L hL y Φ
  have hDr : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Dr).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Dr, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).1]
    funext c g
    simp only [CutMP.dMul, CutMP.drF]
    rw [← List.ofFn_eq_map, List.prod_ofFn]
  have hDrb : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Drb).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drbF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Drb, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).2]
    funext c g
    simp only [CutMP.dMul, CutMP.drbF]
    rw [← List.ofFn_eq_map, List.prod_ofFn, map_prod]
    rfl
  refine ⟨?_, ?_⟩
  · rw [R.LevelData.Ahat, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, Module.End.mul_apply, hDr, R.LevelData.Ar, rds_tprod,
      (rds_vab_ind X L hL y P.r le_rfl Φ).1]
  · rw [R.LevelData.Ahatv, _root_.Formalism.FourierDecayAlt.P5.HerD.pr_fst_mul, Module.End.mul_apply, hDrb, R.LevelData.Avr, rds_tvprod,
      (rds_vabm_ind X L hL y P.r le_rfl Φ).1]

end Formalism.FourierDecayAlt.P.CutSE
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSAGrp\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_A : RDSOpA :=
  rDSOpA_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

theorem spectral_operator_A_adjoint : RDSOpAv :=
  rDSOpAv_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

end Formalism.FourierDecayAlt.P.CutSE
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone =====
