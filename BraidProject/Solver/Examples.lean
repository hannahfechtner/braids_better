import BraidProject.Solver.GroupCorrectnessHardDirection
import BraidProject.Solver.Solver_Fin

open Braid
#eval group_solver [(1, true), (2, true), (4, true), (1, true)]
  [(2, true), (1, true), (2, true), (4, true)]

set_option trace.profiler true
#eval solver_fg (FreeGroup.mk [(1, true), (2, true), (4, true), (1, true)])
  (FreeGroup.mk [(2, true), (1, true), (2, true), (4, true)])
#eval braid_solver (σ 1 * σ 2 * σ 1) (σ 2 * σ 1 * σ 2 * (σ 3)⁻¹* (σ 3))

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

#check Classical.choose
