module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianFamilyHodgeLattice
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMap
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLabelFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponent
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartHodgeComponentLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree

alias expCover_mem_punct := _root_.GlobalTheory.CompanionTheory.Ar.Flat.Link.expCover_mem_punct

theorem exists_actPeriods_chart_data (hG : Top.Given) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
    {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W}
    {Hd : HodgeData Dc} {S₀ : Finset ℕ} (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts)
    (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)
    (ht₀ : t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1))
    (z₀ : Sp ℂ ⟶ Or.𝔐.X) (hz₀ : CoordsAt Or.𝔐.ξ Dc.y z₀ ((Dc.chart a).γ t₀))
    (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
    (hsm : Or.IsSmallPart d s) :
    ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ₁ ρ₂ : ℝ)
      (σ₀ : KA l →+* ℂ) (C : Flat.BdryChart (Xo l) σ₀ (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀)
      (jj : Sp C.R ⟶ Or.𝔐.X) (m : SABMap C.t Or.𝔐.t jj)
      (sc : CMType H × Fin (Dc.N - Dc.j) → Fin C.g → C.R)
      (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ)
      (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ C.g Λ)
      (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ₂) C.ψ)
      (σa : CMType H ⊕ CMType H → (𝓞 E →+* ℂ)),
      let pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X) :=
        fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj
      let b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin C.g → ℂ :=
        fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i)
      0 < ρ₁ ∧ 0 < ρ₂ ∧ ρ₂ ≤ 1 ∧
      IsCMFam (fun τ => σa (Or.sm τ)) ∧
      IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B (fun τ => σa (Or.sm τ)) b ∧
      (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1),
        t₀ + ((ρ₁ * ρ₂ : ℝ) : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧
        InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + ((ρ₁ * ρ₂ : ℝ) : ℂ) • (u ∘ π))) ∧
        CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + ((ρ₁ * ρ₂ : ℝ) : ℂ) • (u ∘ π))) ∧
        Or.𝔐.LabVal (pt u) Or.sm (fun τ => σa (Or.sm τ)) ∧
        (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧
      (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le),
        ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G),
          (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧
          FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) ∧
      (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le,
        (∀ p, p ∈ e.per ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) ↔ ∃ x, L.P w x = p) ∧
        ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1) ∧
        ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ Or.𝔐.t.G.left)
          (u : HolUnif A (Or.𝔐.t.PP.L.pull φ) C.g) (χ' : u.Λ → ℂ),
          IsGrpPullback A Or.𝔐.t.G (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) φ ∧
          u.IsAH (L.H (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) χ' ∧
          (∀ x, (u.ex x).left ≫ φ = (e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) x).left ≫ m.φ) ∧
          (∀ x, x ∈ u.Λ ↔ x ∈ e.per ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w))) ∧
      (∀ c x, e.ex ((ρ₂ : ℂ) • 0) (L.B 0 c x) = e.ex ((ρ₂ : ℂ) • 0) x ≫ C.t.act.act c) ∧
      (∀ i, ∃ v : epsAt (pt 0) ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt (pt 0) (s i.1 i.2) v ∧
        v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ ((ρ₂ : ℂ) • 0))) ≫ (C.M.pt (sc i)).left ≫ m.φ) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpq : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  have hfr := (((_root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀).2 d).2 s hsm).1
  have hval0 : ∀ i : CMType H × Fin (Dc.N - Dc.j), ∃ v : epsAt z₀ ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt z₀ (s i.1 i.2) v := fun i =>
    _root_.GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z₀ (Or.sm i.1) _ (s i.1) (Or.𝔐.all _) (hfr i.1 _) i.2
  obtain ⟨a₀, π, ρ₁, σ₀, C, jj, m, sc, hρ₁, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 _ Dc.Bd (Dc.chart a) t₀
    d.c d.f (CMType H × Fin (Dc.N - Dc.j)) (fun i => s i.1 i.2) z₀ Or.bd ht₀ hz₀ d.inDom hval0
  obtain ⟨ρ₂, Λ, _, L₀, e, hρ₂, hρ₂1, hper, hRiem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem E H D l (Xo l) σ₀ _ a₀ C hpq
  obtain ⟨Bf, hBd, hBe⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family E H C.R C.t C.g _ C.M ρ₂ C.ψ e hρ₂
  have hnorm : ∀ u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ, ‖(ρ₂ : ℂ) • u‖ = ρ₂ * ‖u‖ := fun u => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ₂.le]
  have hsmρ : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ρ₂ := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [hnorm]
    nlinarith
  have hsm1 : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := fun u hu =>
    Metric.ball_subset_ball hρ₂1 (hsmρ u hu)
  have hsmd : DifferentiableOn ℂ (fun u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ => (ρ₂ : ℂ) • u)
      (Metric.ball 0 1) := (differentiable_id.fun_const_smul _).differentiableOn
  have hBhol : ∀ c x, DifferentiableOn ℂ (fun z => Bf ((ρ₂ : ℂ) • z) c x) (Metric.ball 0 1) := fun c x =>
    (hBd c x).comp hsmd hsmρ
  have hpb : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le,
      GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := fun w hw => expCover_mem_punct L₀.a_le hw
  have hclosed : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, ∀ c x, ∃ y, L₀.P w y =
      Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) c (L₀.P w x) := by
    intro w hw c x
    have hb := hsmρ _ (hpb w hw).1
    have h1 : e.ex _ (L₀.P w x) = 1 := ((hper w hw _).2 ⟨x, rfl⟩ : _)
    refine (hper w hw _).1 ?_
    show e.ex _ _ = 1
    rw [hBe _ hb, h1]
    haveI := C.t.act.hom c
    simp
  obtain ⟨instM, hact⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action E _ a₀ C.g Λ L₀ (fun z => Bf ((ρ₂ : ℂ) • z)) hBhol hclosed
  have hInt : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ u ∈ Flat.punct _ a₀ 1) := by
    intro u hu
    obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 u hu)
    have h5 := Or.bd _ _ h3
    have h6 : Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ (ρ₂ : ℂ) • u ∈ Flat.punct _ a₀ 1 := by
      rw [← h4, h5, not_not]
    rw [h6]
    have hne : (ρ₂ : ℂ) ≠ 0 := by exact_mod_cast hρ₂.ne'
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hu, fun i hi h0 => h i hi (by simp [h0])⟩
    · rintro ⟨-, h⟩
      exact ⟨hsm1 u hu, fun i hi => by simpa [hne] using h i hi⟩
  have hF : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, _ := fun w hw =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 σ₀ _ a₀ C jj m (Metric.ball 0 ρ₂) e
      ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) (Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w))
      (L₀.H (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) hpq (hsmρ _ (hpb w hw).1)
      ((hInt _ (hpb w hw).1).2 (hpb w hw)) (hRiem _ (hpb w hw)) (hBe _ (hsmρ _ (hpb w hw).1))
  have hinj : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, Function.Injective (L₀.P w) := by
    intro w hw
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine L₀.unimod.1 ?_
    ext y
    have h := L₀.im w hw x y
    rw [hx] at h
    simpa using h.symm
  have hw₀ : ∃ w₀, w₀ ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le := by
    refine ⟨fun k => if (k : ℕ) < a₀ then -1 else 0, fun i => ?_, fun k hk => ?_⟩
    · simp
    · simp [not_lt.2 hk]
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hadj : ∀ c c' : 𝓞 E, (c' : E) = IsCMField.complexConj E (c : E) → ∀ x y, L₀.E (c • x) y = L₀.E x (c' • y) := by
    intro c c' hc x y
    obtain ⟨A, _, φ, u, χ', -, -, -, -, -, h⟩ := hF w₀ hw₀
    have h1 := L₀.im w₀ hw₀ (c • x) y
    have h2 := L₀.im w₀ hw₀ x (c' • y)
    rw [hact w₀ hw₀] at h1
    rw [hact w₀ hw₀] at h2
    have h3 := h c c' hc (L₀.P w₀ x) (L₀.P w₀ y)
    have h4 : ((L₀.E (c • x) y : ℤ) : ℝ) = ((L₀.E x (c' • y) : ℤ) : ℝ) := by
      rw [← h1, ← h2]
      exact congrArg Complex.im h3
    exact_mod_cast h4
  let L : ActPeriods E _ a₀ C.g Λ :=
    { toLogPeriods := L₀
      adj := hadj
      B := fun z => Bf ((ρ₂ : ℂ) • z)
      B_hol := hBhol
      act := hact }
  obtain ⟨σa, hσ, hinl, hinr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R jj _ C.ψ C.hol
  have hcm : IsCMFam (fun τ => σa (Or.sm τ)) := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h]
    · exact hinr
    · exact hinl
  have hdiffb : ∀ (r : C.R), DifferentiableOn ℂ (fun u => C.ψ ((ρ₂ : ℂ) • u) r) (Metric.ball 0 1) := fun r =>
    (C.hol.2 r).comp hsmd hsm1
  have hframe : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∀ τ
      (h : genPt Or.𝔐.ξ ⤳ centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj)),
      (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj), h⟩ := by
    intro u hu τ h
    obtain ⟨-, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    have h4 := (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ h3).2 { d with inDom := h2 }
    exact (h4.2 s hsm).1 τ h
  have h0 : (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∈
      Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨a₀, π, ρ₁, ρ₂, σ₀, C, jj, m, sc, Λ, inferInstance, instM, L, e, σa,
    hρ₁, hρ₂, hρ₂1, hcm, ⟨fun τ k => differentiableOn_pi.2 fun i => hdiffb _, fun t ht τ => ?_⟩,
    fun u hu => ?_, fun w hw => ?_, fun w hw => ?_, hBe _ (hsmρ 0 h0), (hA _ (hsm1 0 h0)).2.2.2.2⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R C.t jj m C.g _ C.M (Metric.ball 0 ρ₂) C.ψ e ((ρ₂ : ℂ) • t)
      (Bf ((ρ₂ : ℂ) • t)) (Or.sm τ) _ (s τ) (fun k => sc (τ, k)) σa (hsmρ t ht) (hBe _ (hsmρ t ht))
      (hσ _ (hsm1 t ht)) (hframe t ht τ) (fun k => (hA _ (hsm1 t ht)).2.2.2.2 (τ, k))
  · have heq : t₀ + (((ρ₁ * ρ₂ : ℝ)) : ℂ) • (u ∘ π) = t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • u) ∘ π) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      push_cast
      ring
    rw [heq]
    obtain ⟨h1, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    exact ⟨h1, h2, h3, fun i a' => hσ _ (hsm1 u hu) (Or.sm i) a', hInt u hu⟩
  · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, hdv, -⟩ := hF w hw
    have hbρ := hsmρ _ (hpb w hw).1
    choose v hv1 hv2 using (hA _ (hsm1 _ (hpb w hw).1)).2.2.2.2
    refine ⟨v, fun i => hv1 i, ?_⟩
    refine ⟨A, instA, φ, u, χ', hgp, hAH, fun a' p => ?_, hinj w hw, fun p => ?_, fun i => ?_⟩
    · show (u.ex (Bf _ a' p)).left ≫ φ = _
      have e1 : (u.ex p).left ≫ φ ≫ (Or.𝔐.t.act.act a').left = ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ (Or.𝔐.t.act.act a').left := by
        rw [← hex p, Category.assoc]
      rw [hex, e1, hBe _ hbρ, Over.comp_left, Category.assoc, Category.assoc, m.act]
    · rw [hlat p]
      exact hper w hw p
    · obtain ⟨v', h1, h2⟩ := hdv _ _ (Flat.FrameDeriv.isDerivAt0_pt e hbρ (sc i))
      exact ⟨v', by rw [h1, hv2 i, Category.assoc], h2⟩
  · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, -, -⟩ := hF w hw
    obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 _ (hpb w hw).1)
    exact ⟨hper w hw, h4.1 fun hb => (Or.bd _ _ h3).1 hb ((hInt _ (hpb w hw).1).2 (hpb w hw)),
      A, instA, φ, u, χ', hgp, hAH, hex, hlat⟩

theorem exists_actPeriods_chart : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts), ∀ t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ Or.IsSmallPart d s ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) := by
  intro hG E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or a t₀ ht₀
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨z₀, -, hz₀⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie ((Dc.chart a).γ t₀)).1 ((Dc.chart a).mem t₀ ht₀)
  obtain ⟨⟨d⟩, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀
  obtain ⟨⟨s, hsm⟩, -⟩ := hd d
  obtain ⟨a₀, π, ρ₁, ρ₂, _, C, jj, _, sc, Λ, instA, instM, L, _, σa, hρ₁, hρ₂, -, hcm, hEig, hU, hV, -, -, -⟩ :=
    exists_actPeriods_chart_data hG Or a t₀ ht₀ z₀ hz₀ d s hsm
  exact ⟨a₀, C.g, Λ, instA, instM, L, π, ρ₁ * ρ₂, fun τ => σa (Or.sm τ),
    fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj, d, s, fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i),
    mul_pos hρ₁ hρ₂, hcm, hsm, hEig, hU, hV⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree
