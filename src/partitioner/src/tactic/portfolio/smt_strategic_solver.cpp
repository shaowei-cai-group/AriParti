/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_strategic_solver.cpp

Abstract:

    Create a strategic solver with tactic for all main logics
    used in SMT.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include "cmd_context/cmd_context.h"
#include "solver/tactic2solver.h"
#include "solver/solver2tactic.h"
#include "params/tactic_params.hpp"
#include "parsers/smt2/smt2parser.h"
#include "math/subpaving/tactic/subpaving_tactic.h"

class smt_strategic_solver_factory : public solver_factory {
    symbol m_logic;
public:
    smt_strategic_solver_factory(symbol const & logic):m_logic(logic) {}

    solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) override {
        symbol l;
        if (m_logic != symbol::null)
            l = m_logic;
        else
            l = logic;
        tactic_ref t = mk_subpaving_tactic(m, p);
        return mk_tactic2solver(m, t.get(), p, proofs_enabled, models_enabled, unsat_core_enabled, l);
    }
};

solver_factory * mk_smt_strategic_solver_factory(symbol const & logic) {
    return alloc(smt_strategic_solver_factory, logic);
}


