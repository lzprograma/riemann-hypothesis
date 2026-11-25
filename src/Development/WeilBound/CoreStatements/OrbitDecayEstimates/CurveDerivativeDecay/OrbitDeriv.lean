module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HasDerivAtCurve
public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

theorem interp {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {M η τ a : ℝ} (hM : 0 ≤ M)
    (hL : ∀ s t, ‖f' s - f' t‖ ≤ M * |s - t|) (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖f s‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : ‖f a - f 0‖ ≤ (2 * η / τ + M * τ) * a := by
  have key : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f' s‖ ≤ 2 * η / τ + M * τ := fun s hs => by
    have hg : ∀ t ∈ Set.Icc (0 : ℝ) τ, HasDerivWithinAt (fun t : ℝ => f (s + t) - (t : ℂ) * f' s)
        (f' (s + t) - f' s) (Set.Icc 0 τ) t := fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => f (s + t)) (f' (s + t)) t := by
        simpa [Function.comp_def] using (hf (s + t)).scomp t ((hasDerivAt_id' t).const_add s)
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * f' s) (f' s) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (f' s)
      exact (h1.sub h2).hasDerivWithinAt
    have hb : ∀ t ∈ Set.Ico (0 : ℝ) τ, ‖f' (s + t) - f' s‖ ≤ M * τ := fun t ht =>
      (hL _ _).trans <| mul_le_mul_of_nonneg_left (by rw [add_sub_cancel_left, abs_of_nonneg ht.1]; exact ht.2.le) hM
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb τ ⟨hτ.le, le_rfl⟩
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at hmv
    have htri : ‖(τ : ℂ) * f' s‖ ≤ ‖f (s + τ) - (τ : ℂ) * f' s - f s‖ + ‖f (s + τ)‖ + ‖f s‖ := by
      have : (τ : ℂ) * f' s = -(f (s + τ) - (τ : ℂ) * f' s - f s) + f (s + τ) - f s := by ring
      conv_lhs => rw [this]
      exact (norm_sub_le _ _).trans <| add_le_add ((norm_add_le _ _).trans_eq (by rw [norm_neg])) le_rfl
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le] at htri
    rw [div_add' _ _ _ hτ.ne', le_div_iff₀ hτ]
    nlinarith [hη (s + τ) ⟨by linarith [hs.1], by linarith [hs.2]⟩, hη s ⟨hs.1, by linarith [hs.2]⟩]
  simpa using norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x _ => (hf x).hasDerivWithinAt) (fun x hx => key x ⟨hx.1, by linarith [hx.2, ha.2]⟩) a ⟨ha.1, le_rfl⟩

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem orbit_deriv (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (actM (smE ε π) Z x : smD ε π)) s := by
  have hu0 : uMat (c 0) = 1 := by rw [h0]; rfl
  have hev : ∀ᶠ t : ℝ in 𝓝 0, inUJ ε (uMat (c t)) := Filter.Eventually.of_forall fun t => (c t).2
  have hd0 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) 0 := by
    have h1 := hasDerivAt_curve hπ x.2 hu0 hc hev
    rwa [dS_eq_actM (isDerivedOn_smE hπ) (inG_of_curve hu0 hc hev) x] at h1
  have h2 := (((π (uMat (c s))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s - s)
    (by rwa [sub_self])).comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : c t = c s * c (t - s) := by rw [← hadd]; congr 1; ring
  show π (uMat (c t)) (x : H) = π (uMat (c s)) (π (uMat (c (t - s))) x)
  rw [e, show uMat (c s * c (t - s)) = uMat (c s) * uMat (c (t - s)) from rfl,
    hπ.1.2 _ (c s).2 _ (c (t - s)).2]
  rfl

theorem coef_interp (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) {u : H}
    (hu : ‖u‖ ≤ 1) {M η τ a : ℝ} (hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ M)
    (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (c s)) (x : H), u⟫_ℂ‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ‖⟪π (uMat (c a)) (x : H), u⟫_ℂ - ⟪π (uMat (c 0)) (x : H), u⟫_ℂ‖ ≤ (2 * η / τ + M * τ) * a := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  set y : smD ε π := actM (smE ε π) Z x
  have hF := orbit_deriv hπ x h0 hadd hc
  have hG := orbit_deriv hπ y h0 hadd hc
  have hf : ∀ s, HasDerivAt (fun t : ℝ => ⟪π (uMat (c t)) (x : H), u⟫_ℂ) ⟪π (uMat (c s)) (y : H), u⟫_ℂ s :=
    fun s => by simpa using (hF s).inner ℂ (hasDerivAt_const s u)
  have hL : ∀ s t, ‖⟪π (uMat (c s)) (y : H), u⟫_ℂ - ⟪π (uMat (c t)) (y : H), u⟫_ℂ‖ ≤ M * |s - t| := fun s t => by
    rw [← inner_sub_left]
    have hmv : ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ ≤ M * |s - t| := by
      simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r _ => (hG r).hasDerivWithinAt) (fun r _ => by rwa [hπ.2.1 _ (c r).2])
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
    exact (norm_inner_le_norm _ _).trans <|
      (mul_le_mul hmv hu (norm_nonneg _) (mul_nonneg hM0 (abs_nonneg _))).trans_eq (mul_one _)
  exact interp hf hM0 hL hη hτ hτ1 ha

theorem inner_move (hπ : IsURepOn (UJset ε) π) (g k : UJ ε) (a b : H) :
    ⟪π (uMat g) a, π (uMat k) b⟫_ℂ = ⟪a, π (uMat (g⁻¹ * k)) b⟫_ℂ := by
  have hk : uMat k = uMat g * uMat (g⁻¹ * k) := congrArg uMat (mul_inv_cancel_left g k).symm
  rw [hk, hπ.1.2 _ g.2 _ (g⁻¹ * k).2, ContinuousLinearMap.comp_apply]
  exact ({ toLinearMap := (π (uMat g)).toLinearMap, norm_map' := hπ.2.1 _ g.2 } : H →ₗᵢ[ℂ] H).inner_map_map a _

theorem low_bounds {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hB : ∀ a, |lam a| ≤ B) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π)
    (hv1 : ‖v‖ = 1) : ∃ x : smD ε π, (x : H) = v ∧ (∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2)) ∧
      ∀ Z, ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ hs Z * (8 * Real.sqrt m * (B + 2)) ^ 2 := by
  obtain ⟨hv_s, hW⟩ := kFiniteWordBound_indefUnitary m ε lam B H π hm hl hDS hB hg v hv
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  let x : smD ε π := ⟨v, (mem_smD_iff ε π v).2 fun g₀ hg₀ => hv_s g₀ hg₀⟩
  have hC : ∀ W : List (Matrix (Fin m) (Fin m) ℂ), W.length ≤ 2 → (∀ X ∈ W, hs X ≤ 1) →
      ‖PI.DSInfCharCap.dsigCW ε π W v‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ W.length := fun W hl1 hX => by
    simpa [hv1] using hW 2 W hl1 hX
  have one : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2) := fun X hX => by
    have e : PI.DSInfCharCap.dsigCW ε π [X] v = (actM (smE ε π) X x : H) := dsigC_eq_actM hπ X x
    simpa [e] using hC [X] (by simp) (by simpa using hX)
  have two : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X (actM (smE ε π) X x)‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ 2 := fun X hX => by
    have h := hC [X, X] (by simp) (by simp [hX])
    have e : PI.DSInfCharCap.dsigCW ε π [X, X] v = (actM (smE ε π) X (actM (smE ε π) X x) : H) := by
      show PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigC ε π X (x : H)) = _
      rw [dsigC_eq_actM hπ X x, dsigC_eq_actM hπ X]
    simpa [e] using h
  refine ⟨x, rfl, one, fun Z => ?_⟩
  have hnn : 0 ≤ hs Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [eq_zero_of_hs h0.symm]
    have hz := actM_smul (actM (smE ε π) 0 x) 0 (0 : Matrix (Fin m) (Fin m) ℂ)
    simp only [Complex.ofReal_zero, zero_smul] at hz
    simp [hz, hs]
  · set a := (Real.sqrt (hs Z))⁻¹
    have ha0 : 0 ≤ a := by positivity
    have hY : hs ((a : ℂ) • Z) ≤ 1 := by rw [hs_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    have h := two _ hY
    rw [actM_smul, actM_smul, map_smul, norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg ha0] at h
    have ha2 : a * a * hs Z = 1 := by rw [← sq, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le, norm_nonneg (actM (smE ε π) Z (actM (smE ε π) Z x))]

end CompanionTheory.Lime.T3
