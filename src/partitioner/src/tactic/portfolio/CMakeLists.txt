z3_add_component(portfolio
  SOURCES
    default_tactic.cpp
    smt_strategic_solver.cpp
    solver2lookahead.cpp
    solver_subsumption_tactic.cpp
  COMPONENT_DEPENDENCIES
    sat_solver
    sls_tactic
    subpaving_tactic
  TACTIC_HEADERS
    default_tactic.h
    solver_subsumption_tactic.h

)
