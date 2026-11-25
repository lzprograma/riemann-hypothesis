module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

noncomputable section
namespace GlobalTheory.GtAnModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPts GlobalTheory.ToricData GlobalTheory.ToricDict GlobalTheory.HostModel Out.Inh Out.InhTate

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}


variable (l) in
def splitArc : letI := H.starRing; AnArc (𝓞 E) :=
  letI := H.starRing
  { gB := 0
    abelian₂ := ⊥
    discrete := inferInstance
    full := Subsingleton.elim _ _
    Hm := 0
    Hm_herm := Matrix.isHermitian_zero
    Hm_pos := fun z hz => absurd (Subsingleton.elim _ _) hz
    Ef := 0
    Ef_eq := fun l m => by simp [hermForm]
    Ef_bij := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    chi := fun _ => 1
    chi_norm := fun _ => norm_one
    chi_add := fun l m => by simp [hermForm]
    chi_neg := fun _ => rfl
    F := { toFun := fun _ => 0
           map_one' := Subsingleton.elim _ _
           map_mul' := fun _ _ => Subsingleton.elim _ _
           map_zero' := rfl
           map_add' := fun _ _ => Subsingleton.elim _ _ }
    F_mem := fun a l _ => Subsingleton.elim (α := Fin 0 → ℂ) _ _
    F_adj := fun a z w => by simp [hermForm]
    X := 𝓞 E
    ct := 0
    ct_smul := fun _ _ => Subsingleton.elim _ _
    T := 0
    T_symm := fun _ _ => rfl
    T_adj := fun _ _ _ => rfl
    psi := fun _ => 1
    psi_neg := fun _ => rfl
    psi_add := fun _ _ => by simp
    be := arcForm l
    be_symm := fun y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
    be_pos := fun y hy => mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
    be_adj := fun a y z => congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
    be_even := fun y => ⟨l.M' * trForm H y y, mul_assoc _ _ _⟩ }

theorem isTangent_zero (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : IsTangent v := by
  have h : v.left = spMap (algebraMap ℂ (DualNumber ℂ)) := (Category.comp_id _).symm.trans (Over.w v)
  have h' : η[(zeroPolAV (Sp ℂ)).A].left = 𝟙 (Sp ℂ) :=
    (Category.comp_id _).symm.trans (Over.w η[(zeroPolAV (Sp ℂ)).A])
  unfold IsTangent
  rw [h, h']
  refine (Spec.map_comp _ _).symm.trans ?_
  exact Spec.map_id _

theorem isDiff_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) [IsEmpty (Fin A.gB)] (w : Fin A.gB → ℂ)
    (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : (zeroUnif A).IsDiff w v := by
  intro U h f
  have hv : v.left ≫ 𝟙 (Sp ℂ) = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [map_zero]
  have hf : f = constFn (𝟙 (Sp ℂ)) U (valAt' (𝟙 (Sp ℂ)) U f) := by
    refine ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx hU => ?_
    obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
    exact (valAt'_constFn _ _ (Category.comp_id _) _ _ hU).symm
  have e := GlobalTheory.Points.valR_constFn_of_over (𝟙 (Sp ℂ)) (algebraMap ℂ (DualNumber ℂ)) v.left hv U h (valAt' (𝟙 (Sp ℂ)) U f)
  have e' := (congrArg (valR v.left U) hf).trans e
  unfold valR at e'
  rw [dite_eq_left h] at e'
  exact (congrArg TrivSqZeroExt.snd e').trans rfl

variable (c : Coeff l) (bF : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

def model : letI := H.starRing; GtAn (arcIn c ℂ bF) :=
  letI := H.starRing
  letI : IsEmpty (Fin (splitArc l).gB) := inferInstanceAs (IsEmpty (Fin 0))
  let d := dict (splitArc l) (fun _ => 1) (fun _ => by simp [splitArc]) (polar_one_smul ℂ)
  { star_eq := rfl
    A := splitArc l
    ε := LinearEquiv.refl _ _
    be_eq := fun _ _ => rfl
    gB_eq := rfl
    u := zeroUnif (splitArc l)
    lam := rfl
    ah := d.isAH
    rig := d.isRig
    tan := ⟨fun v _ => ⟨0, isDiff_zero (splitArc l) 0 v, fun _ _ => Subsingleton.elim _ _⟩,
      fun w => ⟨toUnit _, ⟨isTangent_zero _, isDiff_zero (splitArc l) w _⟩, fun _ _ => toUnit_unique _ _⟩⟩
    pow := fun n => by
      have hθ : ∀ θ, (zeroUnif (splitArc l)).IsThetaFn (splitArc l).Hm (fun m => (splitArc l).chi ⟨m.1, m.2⟩) n θ :=
        fun θ => ⟨(mem_Theta (splitArc l) n 0 θ).1, fun m z => by
          have := (mem_Theta (splitArc l) n 0 θ).2 ⟨m.1, m.2⟩ z
          rw [map_zero, AnArc.H_zero_left, mul_zero, Complex.exp_zero, _root_.mul_one] at this
          exact this⟩
      have key : ∀ s θ, (zeroUnif (splitArc l)).IsFnPow n s θ ↔
          valAt' (𝟙 (Sp ℂ)) _ (s.f fun _ => PUnit.unit) = θ 0 := fun s θ =>
        ⟨fun h => (h (fun _ => PUnit.unit) 0 (wchart_triv _ _).ge).trans (by simp [zeroUnif]), fun h j z _ => by
          obtain rfl : z = 0 := Subsingleton.elim (α := Fin 0 → ℂ) _ _
          exact h.trans (by simp [zeroUnif])⟩
      refine ⟨fun s => ⟨fun _ => _, ⟨hθ _, (key _ _).2 rfl⟩, fun θ h => funext fun z => ?_⟩, fun θ _ => ?_⟩
      · obtain rfl : z = 0 := Subsingleton.elim (α := Fin 0 → ℂ) _ _
        exact ((key _ _).1 h.2).symm
      · have hc : ∀ i, valAt' (𝟙 (Sp ℂ)) ((lbPow (zeroPolAV (Sp ℂ)).L n).U i) (constFn (𝟙 (Sp ℂ)) _ (θ 0)) = θ 0 :=
          fun i => valAt'_constFn _ _ (Category.comp_id _) _ _ (wchart_triv _ _).ge
        refine ⟨⟨fun i => constFn (𝟙 (Sp ℂ)) _ (θ 0), fun i i' => ?_⟩, (key _ _).2 (hc _), ?_⟩
        · obtain rfl : i = i' := funext fun _ => rfl
          erw [linComb_triv_g]
          exact (_root_.one_mul _).symm
        · rintro ⟨f, hf⟩ h
          congr 1
          funext i
          refine ComplexPoints.eq_of_valAt'_eq (𝟙 (Sp ℂ)) _ _ _ fun x hx _ => ?_
          obtain rfl : x = 𝟙 _ := (Category.comp_id _).symm.trans hx
          exact ((key _ _).1 h).trans (hc _).symm
    act := fun _ _ => toUnit_unique _ _
    ct := fun _ => toUnit_unique _ _
    psi := fun x => by
      refine (congrArg₂ (· / ·) (d.psi_val x _ le_top) (frameProd_zeroUnif (splitArc l) _ _ _)).trans ?_
      change (1 : ℂ) * (1 : ℂ)⁻¹ / 1 = 1
      simp
    ex0 := d.ex₀
    ex0_b := d.ex₀_b_left
    arcDict_expZero_section := fun v x => by
      refine (congrArg₂ (· / ·) (valAt'_gv_unitOn _ (wchart_triv _ _).ge) (frameProd_zeroUnif (splitArc l) _ _ _)).trans ?_
      exact div_one _ }

end Model

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
  {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GlobalTheory.ArcPts.GtAn a)

open FrameValue


include Λ in
theorem isScalarTower : IsScalarTower ℂ (FractionRing ℂ) ℂ := by
  have h : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) :=
    (Over.w (Λ.ex0 0).b).symm.trans ((congrArg (· ≫ a.D₀.P.A.hom) (Λ.ex0_b 0)).trans (Over.w (Λ.u.ex _)))
  rw [← Spec.map_comp, ← Spec.map_id] at h
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  exact IsScalarTower.of_algebraMap_eq' h'.symm

theorem ex_zero : Λ.u.ex 0 = η[a.D₀.P.A] :=
  GlobalTheory.ArcOfModel.ex_zero Λ.u

theorem analyticTorusPoint_base_eq_holUnif_ex (v : Λ.A.V) : (Λ.ex0 v).b = toUnit _ ≫ Λ.u.ex v.2 := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.analyticTorusPoint_base_eq_holUnif_ex (O := 𝓞 E) (A := Λ.A) (D := a.D₀) (u := Λ.u) Λ.ex0_b v

theorem isLift_gt (v : Λ.A.V) (x : Λ.A.X) :
    IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + v.2, Λ.A.ct x, v.2, 0] := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.is_lift_exponential_zero (ε := Λ.ε) Λ.ct Λ.ex0_b v x

theorem corr_of_genVal {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Sp ℂ ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Sp ℂ ⟶ A.left)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} (hz : IsLift u φ (𝟙 _) z) (hz' : IsLift u φ' (𝟙 _) z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k)
    (h : genVal u hL t (𝟙 _) z = genVal u hL t' (𝟙 _) z') : LB.Gen.Corr L φ ε φ' ε' t t' :=
  TorusExtChar.corr_of_genVal hL ht ht' hz hz' hs h

theorem genVal_mul_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} {p q : ℂ} (h : genVal u hL t y z = p)
    (h' : genVal u hL t' y z' = q) : genVal u hL (LB.mulGen L φ ε φ' ε' t t') y (Sum.elim z z') = p * q :=
  GlobalTheory.ArcOfModel.genVal_mul_of h h'

theorem genVal_inv_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {p : ℂ} (h : genVal u hL t y z = p) :
    genVal u hL (LB.invGen L φ ε t) y z = p⁻¹ :=
  GlobalTheory.ArcOfModel.genVal_inv_of h

theorem genVal_pull_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {f : Y' ⟶ Y} {y : Sp ℂ ⟶ Y'} {y' : Sp ℂ ⟶ Y} (e : y ≫ f = y') {z : K → Fin g → ℂ} {p : ℂ}
    (h : genVal u hL t y' z = p) : genVal u hL (LB.pullGen L φ ε t f) y z = p :=
  GlobalTheory.ArcOfModel.genVal_pull_of e h

theorem genVal_shift (v : Λ.A.V) (z : Fin Λ.A.gB → ℂ) (m : Λ.A.abelian₂) (hv : v.2 = z + m) (x : Λ.A.X) :
    IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct x + z, Λ.A.ct x, z, 0] ∧
    genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct x + z, Λ.A.ct x, z, 0] =
      eTwoPi (v.1 x + Λ.A.H (Λ.A.ct x) m / (2 * Complex.I)) := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.genVal_shift Λ.lam Λ.ah Λ.ct Λ.ex0_b Λ.arcDict_expZero_section v z m hv x

theorem isZero_iff (v : Λ.A.V) : (Λ.ex0 v).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ v = Λ.A.P0 la := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.isZero_iff Λ.lam Λ.ah Λ.ct Λ.ex0_b Λ.arcDict_expZero_section v

theorem isIota (la : Λ.A.La) : Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la)) := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.isIota Λ.lam Λ.ah Λ.rig Λ.ct Λ.psi Λ.ex0_b Λ.arcDict_expZero_section la

theorem isAdd (v v' : Λ.A.V) : (Λ.ex0 v).IsAdd (Λ.ex0 v') (Λ.ex0 (v + v')) := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.isAdd (ε := Λ.ε) Λ.lam Λ.ah Λ.ct Λ.ex0_b Λ.arcDict_expZero_section v v'

theorem analyticTorusPoint_surjective : Function.Surjective Λ.ex0 := by
  have := isScalarTower Λ
  exact GlobalTheory.ArcOfModel.analyticTorusPoint_surjective (ε := Λ.ε) Λ.lam Λ.ah Λ.ct Λ.ex0_b Λ.arcDict_expZero_section

theorem rep_iff (k : ℕ) (p : Out.QkPt a.D₀ (FractionRing ℂ) k) (la : Λ.A.La) :
    Λ.Rep k p la ↔ ∃ q : Out.QkPt a.D₀ ℂ k, QkExt (algebraMap _ ℂ) p q ∧ q.y = Λ.ε la.y ∧
      q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la) := by
  obtain ⟨q, hq, hu⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ)
    (RingHom.ext fun _ => rfl) p
  exact ⟨fun h => ⟨q, hq, h q hq⟩, fun ⟨q', hq', h⟩ q'' hq'' => (hu _ hq'').trans (hu _ hq').symm ▸ h⟩

end General

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

open FrameValue

theorem gtAct (Λ : letI := H.starRing; GlobalTheory.ArcPts.GtAn a) (r : 𝓞 E) (v : letI := H.starRing; Λ.A.V) :
    letI := H.starRing; GtAct a.oa r (Λ.ex0 v) (Λ.ex0 (Λ.A.actV r v)) := by
  letI := H.starRing
  exact GlobalTheory.ArcOfModel.gtAct (ε := Λ.ε) Λ.lam Λ.ah Λ.ct Λ.ex0_b Λ.arcDict_expZero_section Λ.act r v

def toDict (Λ : letI := H.starRing; GlobalTheory.ArcPts.GtAn a) : letI := H.starRing; GtDict a.D₀ a.oa :=
  letI := H.starRing
  { A := Λ.A
    eX := Λ.ε
    u := Λ.u
    lam_eq := Λ.lam
    isAH := Λ.ah
    isRig := Λ.rig
    ex_act := Λ.act
    ex_ct := Λ.ct
    psi_val := fun x j hj => by
      have hz : IsLift Λ.u (fun _ : PUnit => Out.ptK (a.D₀.c (Λ.ε x))) (Out.jFK (R := ℂ) ℂ) fun _ => Λ.A.ct x :=
        fun _ => by
          rw [Λ.ct]
          change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ _ = _
          rw [← Category.assoc, jFK_comp_jK_complex, Category.id_comp]
      refine (valAt'_gen a.D₀.P.isLB (a.D₀.psi_gen _) hz ((hz.le_iff j).2 fun _ => hj)).trans ?_
      rw [Λ.psi, FrameValue.frameProd, Fintype.prod_unique, zpow_neg, zpow_one]
    ex₀ := Λ.ex0
    ex₀_b := analyticTorusPoint_base_eq_holUnif_ex Λ
    chi_val := fun v x j hj =>
      (valAt'_gen a.D₀.P.isLB ((Λ.ex0 v).isGen _) (isLift_gt Λ v x) hj).trans (congrArg (· * _) (Λ.arcDict_expZero_section v x))
    add := isAdd Λ
    onto := analyticTorusPoint_surjective Λ
    lin := gtAct Λ
    ker := isZero_iff Λ
    iota := isIota Λ }

end Bridge

end GlobalTheory.GtAnModel
