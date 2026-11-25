module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic

section
@[expose] public section

open MeasureTheory WeakDual

namespace UpperTheory.Reformulated.B.CharactersSeparatePoints

private theorem comm_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CommCStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A) (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have h1 : gelfandTransform ℂ A (U g * T) ≠ gelfandTransform ℂ A T :=
    fun h => hg ((gelfandTransform_isometry A).injective h)
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.1 h1
  change φ (U g * T) ≠ φ T at hφ
  have hT0 : φ T ≠ 0 := by
    intro h0
    apply hφ
    rw [map_mul, h0, mul_zero]
  have hn : ∀ h, ‖φ (U h)‖ = 1 := by
    intro h
    have : star (φ (U h)) * φ (U h) = 1 := by
      rw [← map_star, ← map_mul, hU, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := congrArg norm this
    rw [norm_mul, norm_star, norm_one] at h2
    nlinarith [norm_nonneg (φ (U h))]
  have hc : Continuous fun h => φ (U h) := by
    have : (fun h => φ (U h)) = fun h => φ (U h * T) / φ T := by
      funext h
      rw [map_mul, mul_div_cancel_right₀ _ hT0]
    rw [this]
    exact ((map_continuous φ).comp hT).div_const _
  refine ⟨{ toFun := fun h => ⟨φ (U h), mem_sphere_zero_iff_norm.2 (hn h)⟩
            map_one' := Circle.ext (by simp)
            map_mul' := fun a b => Circle.ext (by
              change φ (U (a * b)) = φ (U a) * φ (U b)
              rw [map_mul, map_mul])
            continuous_toFun := hc.subtype_mk _ }, ?_⟩
  intro h
  apply hφ
  have : φ (U g) = 1 := congrArg (fun z : Circle => (z : ℂ)) h
  rw [map_mul, this, one_mul]

private theorem alg_case {C A : Type*} [CommGroup C] [TopologicalSpace C] [CStarAlgebra A]
    (U : C →* A) (hU : ∀ h, star (U h) = U h⁻¹) (T : A)
    (hB : ∀ B : A, (∀ h, U h * B = B * U h) → B * T = T * B)
    (hT : Continuous fun h => U h * T)
    {g : C} (hg : U g * T ≠ T) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  let S' : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (Set.range U)
  have mem' : ∀ B, B ∈ S' ↔ ∀ h, U h * B = B * U h := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H h
      exact (H _ ⟨h, rfl⟩).1
    · rintro H _ ⟨h, rfl⟩
      exact ⟨H h, by rw [hU]; exact H _⟩
  let S : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (S' : Set A)
  have mem : ∀ B, B ∈ S ↔ ∀ D ∈ S', D * B = B * D := by
    intro B
    rw [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro H D hD
      exact (H _ hD).1
    · intro H D hD
      exact ⟨H D hD, H _ (star_mem hD)⟩
  have hUS' : ∀ h, U h ∈ S' := fun h => (mem' _).2 fun k => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hUS : ∀ h, U h ∈ S := fun h => (mem _).2 fun D hD => ((mem' D).1 hD h).symm
  have hTS : T ∈ S := (mem _).2 fun D hD => hB D ((mem' D).1 hD)
  have hSS : ∀ B ∈ S, B ∈ S' := fun B hB => (mem' _).2 fun h => (mem _).1 hB _ (hUS' h)
  have hcl : IsClosed (S : Set A) := by
    have : (S : Set A) = ⋂ D ∈ S', {B | D * B = B * D} := by
      ext B
      simp only [SetLike.mem_coe, mem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun D _ => isClosed_eq (by fun_prop) (by fun_prop)
  let _ : CommCStarAlgebra S :=
    { (inferInstance : CStarAlgebra S) with
      mul_comm := fun a b => Subtype.ext ((mem _).1 b.2 _ (hSS _ a.2)) }
  refine comm_case (A := S) (U.codRestrict S hUS) (fun h => Subtype.ext (hU h)) ⟨T, hTS⟩
    (hT.subtype_mk _) (fun h => hg (congrArg Subtype.val h))

private theorem hilbert_case {C H : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [CompactSpace C] [MeasurableSpace C] [BorelSpace C]
    (μ : Measure C) [μ.IsHaarMeasure]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : C →* (H →L[ℂ] H)) (hn : ∀ h v, ‖U h v‖ = ‖v‖) (hc : ∀ v, Continuous fun h => U h v)
    {g : C} {v : H} (hg : U g v ≠ v) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have happ : ∀ a b x, U a (U b x) = U (a * b) x := by
    intro a b x
    rw [map_mul]
    rfl
  have hstar : ∀ h, star (U h) = U h⁻¹ := by
    intro h
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have := (LinearIsometry.mk (U h).toLinearMap (hn h)).inner_map_map (U h⁻¹ x) y
    rw [← this]
    change inner ℂ (U h (U h⁻¹ x)) (U h y) = _
    rw [happ, mul_inv_cancel, map_one]
    rfl
  have hint : ∀ (f : C(C, ℂ)) (x : H), Integrable (fun h => f h • U h x) μ := fun f x =>
    (f.continuous.smul (hc x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T₀ : C(C, ℂ) →ₗ[ℂ] H →ₗ[ℂ] H := LinearMap.mk₂ ℂ (fun f x => ∫ h, f h • U h x ∂μ)
    (fun f f' x => by
      rw [← integral_add (hint f x) (hint f' x)]
      simp [add_smul])
    (fun c f x => by
      rw [← integral_smul]
      simp [mul_smul])
    (fun f x y => by
      rw [← integral_add (hint f x) (hint f y)]
      simp)
    (fun c f x => by
      rw [← integral_smul]
      simp [smul_comm c])
  let T : C(C, ℂ) →L[ℂ] H →L[ℂ] H := T₀.mkContinuous₂ (μ.real Set.univ) (fun f x => by
    have : ‖∫ h, f h • U h x ∂μ‖ ≤ (‖f‖ * ‖x‖) * μ.real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun h => by
        rw [norm_smul, hn]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm h) (norm_nonneg _))
    calc ‖T₀ f x‖ ≤ _ := this
      _ = _ := by ring)
  have hT : ∀ f x, T f x = ∫ h, f h • U h x ∂μ := fun _ _ => rfl
  have hB : ∀ f, ∀ B : H →L[ℂ] H, (∀ h, U h * B = B * U h) → B * T f = T f * B := by
    intro f B hB
    ext x
    change B (T f x) = T f (B x)
    rw [hT, hT, ← B.integral_comp_comm (hint f x)]
    congr 1
    funext h
    rw [map_smul]
    congr 1
    exact (congrArg (fun L : H →L[ℂ] H => L x) (hB h)).symm
  let w : H := U g v - v
  have hw : w ≠ 0 := sub_ne_zero.2 hg
  let f : C(C, ℂ) := ⟨fun h => inner ℂ (U h w) w, (hc w).inner continuous_const⟩
  let F : C(C, C(C, ℂ)) :=
    (f.comp ⟨fun p : C × C => p.1⁻¹ * p.2, by fun_prop⟩).curry
  have hF : ∀ k, U k * T f = T (F k) := by
    intro k
    ext x
    change U k (T f x) = T (F k) x
    rw [hT, hT, ← (U k).integral_comp_comm (hint f x),
      ← integral_mul_left_eq_self (fun h => F k h • U h x) k]
    congr 1
    funext h
    rw [map_smul, happ]
    congr 1
    change f h = f (k⁻¹ * (k * h))
    rw [inv_mul_cancel_left]
  refine alg_case U hstar (T f) (hB f) ?_ ?_
  · simp_rw [hF]
    exact T.continuous.comp F.continuous
  · intro h0
    have h1 : T f w = 0 := by
      have h2 := hB f (U g) (fun h => by rw [← map_mul, ← map_mul, mul_comm])
      rw [h0] at h2
      have h3 : T f v = T f (U g v) := congrArg (fun L : H →L[ℂ] H => L v) h2
      rw [map_sub, ← h3, sub_self]
    have h2 : ∫ h, ((‖f h‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
      have := integral_inner (𝕜 := ℂ) (hint f w) w
      rw [← hT, h1, inner_zero_right] at this
      rw [← this]
      congr 1
      funext h
      rw [inner_smul_right, ← inner_conj_symm w (U h w)]
      change _ = f h * (starRingEnd ℂ) (f h)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1)
      (f := fun h => ‖f h‖ ^ 2) (by fun_prop) (HasCompactSupport.of_compactSpace _)
      (fun h => by positivity) ?_).ne' h2
    have : f 1 = inner ℂ w w := by
      change inner ℂ (U 1 w) w = _
      rw [map_one]
      rfl
    simp only [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))

end UpperTheory.Reformulated.B.CharactersSeparatePoints

theorem UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one.{u_1} :
    ∀ {C : Type u_1} [inst : CommGroup C] [inst_1 : TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
      {g : C}, g ≠ (1 : C) → ∃ (χ : C →ₜ* Circle), (χ : C → Circle) g ≠ (1 : Circle) := by
  intro C _ _ _ _ _ g hg
  borelize C
  let μ : Measure C := Measure.haar
  let m : C(C, C(C, C)) := ContinuousMap.curry ⟨fun p : C × C => p.1 * p.2, by fun_prop⟩
  have hm : ∀ h, MeasurePreserving (m h) μ μ := fun h => measurePreserving_mul_left μ h
  let V : C → (Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ) := fun h => Lp.compMeasurePreservingₗᵢ ℂ (m h) (hm h)
  have hV : ∀ h x, V h x = Lp.compMeasurePreserving (m h) (hm h) x := fun _ _ => rfl
  let U : C →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun h => (V h).toContinuousLinearMap
      map_one' := by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m 1) (hm 1) x = x
        convert Lp.compMeasurePreserving_id_apply x
        funext a
        exact one_mul a
      map_mul' := fun a b => by
        refine ContinuousLinearMap.ext fun x => ?_
        change Lp.compMeasurePreserving (m (a * b)) (hm _) x =
          Lp.compMeasurePreserving (m a) (hm a) (Lp.compMeasurePreserving (m b) (hm b) x)
        rw [← Lp.compMeasurePreserving_comp_apply]
        congr 2
        funext c
        exact (mul_left_comm b a c).trans (mul_assoc a b c).symm |>.symm }
  obtain ⟨F, hF0, hF1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := g)) (isClosed_singleton (x := (1 : C)))
    (Set.disjoint_singleton.2 hg)
  let G : C(C, ℂ) := ⟨fun a => (F a : ℂ), by fun_prop⟩
  refine hilbert_case μ U (fun h x => (V h).norm_map x)
    (fun x => continuous_const.compMeasurePreservingLp m.continuous hm (by simp))
    (v := ContinuousMap.toLp 2 μ ℂ G) ?_
  intro h0
  have h0' : Lp.compMeasurePreserving (m g) (hm g) (ContinuousMap.toLp 2 μ ℂ G) =
      ContinuousMap.toLp 2 μ ℂ G := h0
  have h1 : ContinuousMap.toLp 2 μ ℂ (G.comp (m g)) = ContinuousMap.toLp 2 μ ℂ G := by
    refine Eq.trans (Lp.ext ?_) h0'
    have e1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (G.comp (m g))
    have e2 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 μ ℂ G) (hm g)
    have e3 := (hm g).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ G)
    exact e1.trans (e2.trans e3).symm
  have h2 : (F (g * 1) : ℂ) = F 1 :=
    congrArg (fun f : C(C, ℂ) => f 1) (ContinuousMap.toLp_injective μ h1)
  rw [mul_one, hF0 rfl, hF1 rfl] at h2
  simp at h2
end
end


@[expose] public section

set_option maxSynthPendingDepth 1

open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace GroundTheory.Automorphic.CompactAbelianFourier

noncomputable section

set_option linter.unusedSectionVars false

variable {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  [T2Space C]

section Metrizable

variable [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure C) [μ.IsHaarMeasure]

variable (ψ : C(C, ℝ))


end Metrizable

theorem exists_char_ne {x y : C} (hxy : x ≠ y) : ∃ χ : C →ₜ* Circle, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := _root_.UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one (g := x * y⁻¹) (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

def charCM (χ : C →ₜ* Circle) : C(C, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

theorem charCM_apply (χ : C →ₜ* Circle) (x : C) : charCM χ x = (χ x : ℂ) := rfl

theorem charCM_mul (χ χ' : C →ₜ* Circle) : charCM (χ * χ') = charCM χ * charCM χ' := by
  ext x
  simp [charCM_apply]

theorem charCM_one : charCM (1 : C →ₜ* Circle) = 1 := by
  ext x
  simp [charCM_apply]

theorem star_charCM (χ : C →ₜ* Circle) : star (charCM χ) = charCM χ⁻¹ := by
  ext x
  change conj ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

def charAlgebra : StarSubalgebra ℂ C(C, ℂ) :=
  { (Submodule.span ℂ (Set.range (charCM (C := C)))).toSubalgebra
      (Submodule.subset_span ⟨1, charCM_one⟩)
      (fun a b ha hb => by
        have h := Submodule.mul_mem_mul ha hb
        rw [Submodule.span_mul_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨x, ⟨χ, rfl⟩, y, ⟨χ', rfl⟩, rfl⟩
        exact ⟨χ * χ', charCM_mul χ χ'⟩) with
    star_mem' := fun {a} ha => by
      change a ∈ Submodule.span ℂ (Set.range (charCM (C := C))) at ha
      change star a ∈ Submodule.span ℂ (Set.range (charCM (C := C)))
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact Submodule.subset_span ⟨χ⁻¹, (star_charCM χ).symm⟩
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem charAlgebra_separatesPoints : (charAlgebra (C := C)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨χ, hχ⟩ := exists_char_ne hxy
  exact ⟨charCM χ, ⟨charCM χ, Submodule.subset_span ⟨χ, rfl⟩, rfl⟩, fun h => hχ (Circle.coe_injective h)⟩

theorem span_charCM_dense :
    (Submodule.span ℂ (Set.range (charCM (C := C)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (charAlgebra_separatesPoints (C := C))
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (charAlgebra (C := C)).topologicalClosure := by rw [h]; trivial
  exact hf

end

end GroundTheory.Automorphic.CompactAbelianFourier
