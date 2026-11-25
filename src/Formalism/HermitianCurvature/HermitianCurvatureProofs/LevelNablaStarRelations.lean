module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
public import Formalism.HermitianCurvature.StatementM
public import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx2
open Formalism.FourierDecayAlt.P.Mx4 (comm_eu coord_ne der_fn ec eci eulerComm eulerCoord eulerLeibniz eulerMul euler_GG_z euler_gg_zb euler_inv euler_one gg_ne mk_comm mulOp_add mulOp_mul multiplierPair_add multiplierPair_comm multiplierPair_mul multiplierPair_neg multiplierPair_zero smul_fnP vz_ne)

variable {r : ℕ}

theorem vc_inj (l m : Fin r) : (vc l : Var r) = vc m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vc] using this
  · rintro rfl; rfl
theorem vcb_inj (l m : Fin r) : (vcb l : Var r) = vcb m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vcb] using this
  · rintro rfl; rfl
theorem vc_vcb (l m : Fin r) : (vc l : Var r) ≠ vcb m := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).2) h; simp [vc, vcb] at this
theorem vc_vz (l : Fin r) : (vc l : Var r) ≠ vz := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vc_vzb (l : Fin r) : (vc l : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vcb_vz (l : Fin r) : (vcb l : Var r) ≠ vz := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vcb_vzb (l : Fin r) : (vcb l : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this

end Formalism.FourierDecayAlt.P.Mx2
