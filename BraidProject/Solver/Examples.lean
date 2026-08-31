import BraidProject.Solver.GroupCorrectnessHardDirection


open Braid
#eval group_solver [(1, true), (2, true), (4, true), (1, true)]
  [(2, true), (1, true), (2, true), (4, true)]

#eval solver_fg (FreeGroup.mk [(1, true), (2, true), (4, true), (1, true)])
  (FreeGroup.mk [(2, true), (1, true), (2, true), (4, true)])
#eval! braid_solver (σ 1 * σ 2 * σ 1) (σ 2 * σ 1 * σ 2 * (σ 3)⁻¹* (σ 3))

#eval solver_nonsense ((σ 1 * σ 2 * σ 1)) ((σ 2 * σ 1 * σ 2)⁻¹)


def foo1 := (reverse_word [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1

#eval foo1
#exit
#show_braid_word_help ([[(3, true), (2, true), (0, false), (3, true)],
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))


#show_braid_word_help ([foo1,
  [(3, true), (2, true), (3, true), (0, false)],
  [(2, true), (3, true), (2, true), (0, false)]] : List (List ((ℕ × Bool))))

#eval (reverse_complex [(3, false), (1, true), (2, true), (1, true)]).1
#show_braid_word_help ([(reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1, []] : List (List (ℕ × Bool)))
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1
#eval (reverse_complex [(3, false), (2, true), (2, true), (1, true)]).1.length
#eval (reverse_complex [(2, false), (2, false), (1, false), (1, false), (2, true), (2, true), (1, true), (1, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (4, true), (4, true)]).1.length
#eval (reverse_complex [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1.length

#eval (reverse_complex [(0, false), (0, false), (1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true), (4, true)]).1

#eval (reverse_complex [(1, false), (2, false), (2, false), (3, true), (4, true)]).1.length

-- set_option pp.proofs true in
-- def Quotient.exists_rep_C (a : Quotient new_rels) :
--   Σ b, PLift (Quotient.mk new_rels b = a) := by
--   --apply @Quotient.ind _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--   apply @Quot.hrecOn _ _ (fun x => Σ b, PLift (Quotient.mk new_rels b = x))
--      a (fun c => by use c; constructor; rfl)
--   intro a b hab
--   have H := Quotient.sound hab

--   -- unfold HEq
--   -- simp [H]
--   sorry



-- #check Quot.rec
-- noncomputable def braid_solver (a b : Braid.braid_group_inf) : Bool := by
--   rcases Quotient.exists_rep_C a with ⟨a1, ⟨ha1⟩⟩
--   rcases Quotient.exists_rep_C b with ⟨b1, ⟨hb1⟩⟩
--   sorry



  -- have hb := Classical.choose (Quotient.exists_rep b)
  -- have ha1 := Classical.choose (Quot.exists_rep ha)
  -- have hb1 := Classical.choose (Quot.exists_rep hb)
  -- exact solver_g ha1 hb1


#check Classical.choose
