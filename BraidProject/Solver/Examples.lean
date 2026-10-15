import BraidProject.Solver.GroupCorrectnessHardDirection
import BraidProject.Solver.Solver_Fin

-- 
open Braid
#time
#eval braid_word_solver [(1, true), (2, true), (4, true), (1, true)]
  [(2, true), (1, true), (2, true), (4, true)]

#time
#eval free_group_elem_braid_solver (FreeGroup.mk [(1, true), (2, true), (4, true), (1, true)])
  (FreeGroup.mk [(2, true), (1, true), (2, true), (4, true)])
#eval braid_solver (σ 1 * σ 2 * σ 1) (σ 2 * σ 1 * σ 2 * (σ 3)⁻¹* (σ 3))

#eval solver_nonsense ((σ 1 * σ 2 * σ 1)) ((σ 2 * σ 1 * σ 2)⁻¹)
#time #eval braid_solver
  ((σ 1 * (σ 4)⁻¹ *
    σ 2 * (σ 6)⁻¹ *
    σ 3 * σ 7 *
    (σ 5)⁻¹ * σ 2 *
    (σ 1)⁻¹ * σ 6) ^ 50)

  ((σ 1 * (σ 4)⁻¹ *
    σ 2 * (σ 6)⁻¹ *
    σ 3 * σ 7 *
    (σ 5)⁻¹ * σ 2 *
    (σ 1)⁻¹ * σ 6) ^ 50)

def foo1 := (reverse_word [(1, false), (1, false), (2, false), (2, false), (3, true), (3, true), (4, true)]).1

#eval foo1
