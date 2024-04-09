/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_tactic.cpp

Abstract:

    "Fake" tactic used to test subpaving module.

Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "math/subpaving/tactic/expr2subpaving.h"
#include "ast/expr2var.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include <iostream>
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/tseitin_cnf_tactic.h"
#include "tactic/arith/purify_arith_tactic.h"
#include "util/gparams.h"

class subpaving_tactic : public tactic {

    struct display_var_proc : public subpaving::display_var_proc {
        expr_ref_vector m_inv;
        
        display_var_proc(expr2var & e2v):m_inv(e2v.m()) {
            e2v.mk_inv(m_inv);
        }

        ast_manager & m() const { return m_inv.get_manager(); }
        
        void operator()(std::ostream & out, subpaving::var x) const override {
            expr * t = m_inv.get(x, nullptr);
            if (t != nullptr)
                out << mk_ismt2_pp(t, m());
            else
                out << "k!" << x;
        }
    };

    struct imp {
        enum engine_kind { MPQ, MPF, HWF, MPFF, MPFX, NONE };

        ast_manager &                   m_manager;
        unsynch_mpq_manager             m_qm;
        mpf_manager                     m_fm_core;
        arith_util                      m_autil;
        engine_kind                     m_kind;
        scoped_ptr<subpaving::context>  m_ctx;
        scoped_ptr<display_var_proc>    m_proc;
        expr2var                        m_e2v;
        scoped_ptr<expr2subpaving>      m_e2s;
        bool                            m_display;

        //#linxi
        expr_ref_vector                 m_v2e;
        subpaving::task_info            m_task;
        expr_ref_buffer                 m_expr_buffer;
        expr_ref_vector                 m_task_expr_clauses;
        std::string                     m_output_dir;
        unsigned                        m_max_running_tasks;
        unsigned m_int_var_num;
        unsigned m_nl_val_num;
        symbol m_logic;

        imp(ast_manager & m, params_ref const & p):
            m_manager(m),
            m_autil(m),
            m_kind(NONE),
            m_e2v(m), 
            m_v2e(m),
            m_expr_buffer(m),
            m_task_expr_clauses(m),
            m_int_var_num(0),
            m_nl_val_num(0),
            m_logic()
        {
            updt_params(p);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void collect_param_descrs(param_descrs & r) {        
            m_ctx->collect_param_descrs(r);
            // #ifndef _EXTERNAL_RELEASE
            r.insert("numeral", CPK_SYMBOL, "(default: mpq) options: mpq, mpf, hwf, mpff, mpfx.");
            r.insert("print_nodes", CPK_BOOL, "(default: false) display subpaving tree leaves.");
            // #endif
        }
        
        void updt_params(params_ref const & p) {
            m_display = p.get_bool("print_nodes", false);
            symbol engine = p.get_sym("numeral", symbol("mpq"));
            engine_kind new_kind;
            if (engine == "mpq")
                new_kind = MPQ;
            if (m_kind != new_kind) {
                m_kind = new_kind;
                switch (m_kind) {
                case MPQ:  m_ctx = subpaving::mk_mpq_context(m().limit(), m_qm); break;
                default: UNREACHABLE(); break;
                }
                m_e2s = alloc(expr2subpaving, m_manager, *m_ctx, &m_e2v);
            }
            m_ctx->updt_params(p);
        }

        void collect_statistics(statistics & st) const {
            m_ctx->collect_statistics(st);
        }

        void reset_statistics() {
            m_ctx->reset_statistics();
        }
        
        // return true iff the atom is always TRUE
        bool mk_atom(expr * a, ref_buffer<subpaving::atom, subpaving::context> & atom_buffer) {
            TRACE("linxi_subpaving",
                tout << "mk_atom: " << mk_smt_pp(a, m_manager) << "\n";
            );
            bool neg = false;
            while (m().is_not(a, a))
                neg = !neg;
            bool lower = false;
            bool is_ineq = false;
            bool open = false;
            if (m_manager.is_eq(a)) {
                is_ineq = false;
            }
            else if (m_autil.is_le(a)) {
                is_ineq = true;
                lower = false;
            }
            else if (m_autil.is_ge(a)) {
                is_ineq = true;
                lower = true;
            }
            else if (is_app(a)) {
                // pure boolean variable
                subpaving::var x = m_e2s->internalize_bool_term(a);
                atom_buffer.push_back(m_ctx->mk_bool_atom(x, neg));
                return false;
            }
            else {
                throw tactic_exception("unsupported atom");
            }
            if (neg) {
                lower = !lower;
                open  = !open;
            }
            rational _k;
            if (!m_autil.is_numeral(to_app(a)->get_arg(1), _k))
                throw tactic_exception("use simplify tactic with option :arith-lhs true");
            scoped_mpq k(m_qm);
            k = _k.to_mpq();
            scoped_mpz n(m_qm), d(m_qm);
            subpaving::var x = m_e2s->internalize_term(to_app(a)->get_arg(0), n, d);
            m_qm.mul(d, k, k);
            m_qm.div(k, n, k);
            if (is_neg(n))
                lower = !lower;
            TRACE("subpaving_tactic", tout << x << " " << k << " " << lower << " " << open << "\n";);
            TRACE("linxi_subpaving",
                tout << "x: " << x << ", k: " << k << ", lower: " << lower
                     << ", open: " << open << ", is_ineq: " << is_ineq
                     << ", neg: " << neg << "\n";
            );
            if (is_ineq) {
                if (m_ctx->is_int(x)) {
                    if (!m_qm.is_int(k)) {
                        open = false;
                        if (lower)
                            m_qm.ceil(k, k);
                        else
                            m_qm.floor(k, k);
                    }
                    if (open) {
                        open = false;
                        if (lower)
                            m_qm.inc(k);
                        else {
                            m_qm.dec(k);
                        }
                    }
                }
                atom_buffer.push_back(m_ctx->mk_ineq_atom(x, k, lower, open));
            }
            else {
                if (m_ctx->is_int(x) && !m_qm.is_int(k)) {
                    if (neg) {
                        // int != 3.5 -> sat
                        return true;
                    }
                    else {
                        // int == 3.5 -> unsat
                        return false;
                    }
                }
                TRACE("linxi_subpaving",
                    tout << "mk_eq_atom: " << mk_smt_pp(a, m_manager) << ", neg: " << neg << "\n";
                );
                if (neg) {
                    atom_buffer.push_back(m_ctx->mk_ineq_atom(x, k, false, true));
                    atom_buffer.push_back(m_ctx->mk_ineq_atom(x, k, true, true));
                }
                else {
                    atom_buffer.push_back(m_ctx->mk_eq_atom(x, k, false));
                }
            }
            return false;
        }

        void process_clause(expr * c) {
            TRACE("linxi_subpaving",
                tout << "process_clause: " << mk_smt_pp(c, m_manager) << "\n";
            );
            expr * const * args = nullptr;
            unsigned sz;
            if (m().is_or(c)) {
                args = to_app(c)->get_args();
                sz   = to_app(c)->get_num_args();
            }
            else {
                args = &c;
                sz   = 1;
            }
            ref_buffer<subpaving::atom, subpaving::context> atom_buffer(*m_ctx);
            for (unsigned i = 0; i < sz; i++) {
                if (mk_atom(args[i], atom_buffer))
                    return;
            }
            if (atom_buffer.size() == 0)
                throw tactic_exception("LINXI: unsat by empty clause");
            m_ctx->add_clause(atom_buffer.size(), atom_buffer.data());
        }
        
        void internalize(goal const & g) {
            try {
                for (unsigned i = 0; i < g.size(); i++) {
                    process_clause(g.form(i));
                }
            }
            catch (const subpaving::exception &) {
                throw tactic_exception("failed to internalize goal into subpaving module");
            }
        }

        expr * convert_lit_to_expr(const subpaving::lit & l) {
            expr * ret;
            expr * e = m_v2e[l.m_x].get();
            SASSERT(e != nullptr);
            TRACE("linxi_subpaving",
                tout << "converting expr: " 
                    << mk_smt_pp(e, m()) << "\n";
                tout << "lower: " << l.m_lower << "\n";
                if (!l.m_bool) {
                    tout << "open: " << l.m_open << "\n";
                    tout << "value: ";
                    m_qm.display(tout, *l.m_val);
                    tout << "\n";
                }
                else {
                    if (l.m_open) {
                        tout << "value: ";
                        m_qm.display(tout, *l.m_val);
                        tout << "\n";
                    }
                    else {
                        // do nothing
                    }
                }
            );
            if (l.m_bool) {
                if (l.m_open) {
                    expr_ref val_expr(m());
                    if (l.m_int)
                        val_expr = m_autil.mk_int(*l.m_val);
                    else
                        val_expr = m_autil.mk_real(*l.m_val);
                    ret = m_autil.mk_eq(e, val_expr);
                    if (l.m_lower)
                        ret = m_manager.mk_not(ret);
                }
                else {
                    if (l.m_lower)
                        ret = m_manager.mk_not(e);
                    else
                        ret = e;
                }
            }
            else {
                expr_ref val_expr(m());
                bool is_open = l.m_open;
                if (l.m_int)
                    val_expr = m_autil.mk_int(*l.m_val);
                else
                    val_expr = m_autil.mk_real(*l.m_val);

                if (l.m_lower) {
                    if (is_open)
                        ret = m_autil.mk_gt(e, val_expr);
                    else
                        ret = m_autil.mk_ge(e, val_expr);
                }
                else {
                    if (is_open)
                        ret = m_autil.mk_lt(e, val_expr);
                    else
                        ret = m_autil.mk_le(e, val_expr);
                }
            }
            TRACE("linxi_subpaving",
                tout << "converting expr: " 
                    << mk_smt_pp(e, m())
                    << "\nsuccess\n";
            );
            return ret;
        }

        void collect_bounds_to_buffer(vector<subpaving::lit> &bd) {
            unsigned sz = bd.size();
            if (sz == 1) {
                m_expr_buffer.push_back(convert_lit_to_expr(bd[0]));
                return ;
            }
            subpaving::lit & bl = bd[0], & bu = bd[1];
            // bl.m_x == bu.m_x
            if (!m_qm.eq(*bl.m_val, *bu.m_val)) {
                m_expr_buffer.push_back(convert_lit_to_expr(bl));
                m_expr_buffer.push_back(convert_lit_to_expr(bu));
                return ;
            }
            expr_ref er(m_manager);
            expr * e = m_v2e[bl.m_x].get();
            expr * val;
            if (bl.m_int)
                val = m_autil.mk_int(*bl.m_val);
            else
                val = m_autil.mk_real(*bl.m_val);
            m_expr_buffer.push_back(m_autil.mk_eq(e, val));
        }

        void convert_task_to_exprs() {
            vector<vector<subpaving::lit>> & clauses = m_task.m_clauses;
            for (unsigned i = 0, isz = clauses.size(); i < isz; ++i) {
                vector<subpaving::lit> &cla = clauses[i];
                unsigned jsz = cla.size();
                for (unsigned j = 0; j < jsz; ++j) {
                    subpaving::lit &l = cla[j];
                    m_expr_buffer.push_back(convert_lit_to_expr(l));
                }
                if (jsz > 1) {
                    m_task_expr_clauses.push_back(
                        m_manager.mk_or(m_expr_buffer.size(), m_expr_buffer.data())
                    );
                }
                else {
                    m_task_expr_clauses.push_back(m_expr_buffer[0]);
                }
                m_expr_buffer.reset();
                TRACE("linxi_subpaving",
                    tout << "last expr = "
                        << mk_smt_pp(m_task_expr_clauses.back(), m()) << "\n";
                );
            }
            vector<subpaving::lit> & bounds = m_task.m_var_bounds;
            for (unsigned i = 0, isz = bounds.size(); i < isz; ++i) {
                m_task_expr_clauses.push_back(convert_lit_to_expr(bounds[i]));
            }
            TRACE("linxi_subpaving",
                for (unsigned i = 0, isz = m_task_expr_clauses.size(); i < isz; ++i) {
                    tout << "expr[" << i << "] = "
                        << mk_smt_pp(m_task_expr_clauses[i].get(), m()) << "\n";
                }
            );
        }

        // output current subtask to .smt2 file
        void display_current_task() {
            if (m_logic.is_null()) {
                m_e2s->collect_statistics(m_nl_val_num, m_int_var_num);
                TRACE("linxi_subpaving",
                    tout << "m_nl_val_num = " << m_nl_val_num << "\n";
                    tout << "m_int_var_num = " << m_int_var_num << "\n";
                );
                if (m_nl_val_num > 0) {
                    if (m_int_var_num > 0)
                        m_logic = "QF_NIA";
                    else
                        m_logic = "QF_NRA";
                }
                else {
                    if (m_int_var_num > 0)
                        m_logic = "QF_LIA";
                    else
                        m_logic = "QF_LRA";
                }
            }
            convert_task_to_exprs();
            unsigned sz = m_task_expr_clauses.size();
            if (sz == 0)
                return ;
            std::string task_name;
            {
                std::stringstream ss;
                ss << "task-" << m_task.m_node_id;
                task_name = ss.str();
            }
            std::ofstream ofs(m_output_dir + "/tasks/" + task_name + ".smt2");
            
            ast_smt_pp pp(m());
            pp.set_benchmark_name(task_name.c_str());
            pp.set_logic(m_logic);

            --sz;
            for (unsigned i = 0; i < sz; ++i) {
                pp.add_assumption(m_task_expr_clauses[i].get());
            }
            pp.display_smt2(ofs, m_task_expr_clauses[sz].get());

            m_task_expr_clauses.reset();
        }
        
        lbool solve() {
            lbool res;
            while (true) {
                try {
                    res = (*m_ctx)();
                }
                catch (const subpaving::exception &) {
                    throw tactic_exception("failed building subpaving tree...");
                }
                // l_false: unsat
                if (res == l_false)
                    return l_false;
                // l_undef: 
                //   1. time up. or
                //   2. all splits have been exhausted.
                if (res == l_undef)
                    break;
                // l_sat: generate task successfully
                display_current_task();
            }
            return l_undef;
        }

        void get_params() {
            const params_ref &p = gparams::get_ref();
            m_output_dir = p.get_str("output_dir", "ERROR");
            m_max_running_tasks = p.get_uint("partition_max_running_tasks", 32);
        }

        void process(goal_ref const & g, 
                     goal_ref_buffer & result) {
            TRACE("linxi_subpaving",
                g->display(tout);
                tout << "\n";
            );
            if (g->is_decided()) {
                result.push_back(g.get());
                return;
            }
            lbool res;
            try {
                get_params();
                internalize(*g);
                m_e2v.mk_inv(m_v2e);
                TRACE("linxi_subpaving",
                    for (unsigned i = 0, sz = m_v2e.size(); i < sz; ++i) {
                        expr *e = m_v2e[i].get();
                        if (e != nullptr)
                            tout << "var[" << i << "] = " << mk_smt_pp(m_v2e[i].get(), m_manager) << "\n";
                    }
                );
                m_proc = alloc(display_var_proc, m_e2v);
                m_ctx->set_display_proc(m_proc.get());
                m_ctx->set_task_ptr(&m_task);
                res = solve();
            }
            catch (tactic_exception & ex) {
                if (strcmp(ex.msg(), "LINXI: unsat by empty clause") == 0) {
                    res = l_false;
                }
                else {
                    throw ex;
                }
            }
            
            if (res == l_undef) {
                // do nothing
            }
            else if (res == l_false) {
                g->assert_expr(m().mk_false(), nullptr, nullptr);
            }
            else {
                UNREACHABLE();
                // TBD
            }

            g->inc_depth();
            result.push_back(g.get());
            //#linxi
            // m_display = true;
            if (m_display) {
                m_ctx->display_constraints(std::cout);
                std::cout << "bounds at leaves: \n";
                m_ctx->display_bounds(std::cout);
            }
        }
    };
    
    imp *       m_imp;
    params_ref  m_params;
    statistics  m_stats;
public:

    subpaving_tactic(ast_manager & m, params_ref const & p):
        m_imp(alloc(imp, m, p)),
        m_params(p) {
    }

    ~subpaving_tactic() override {
        dealloc(m_imp);
    }

    char const* name() const override { return "subpaving"; }

    tactic * translate(ast_manager & m) override {
        return alloc(subpaving_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_imp->updt_params(m_params);
    }

    void collect_param_descrs(param_descrs & r) override {
        m_imp->collect_param_descrs(r);
    }

    void collect_statistics(statistics & st) const override {
        st.copy(m_stats);
    }

    void reset_statistics() override {
        m_stats.reset();
    }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        try {
            m_imp->process(in, result);
            m_imp->collect_statistics(m_stats);
        }
        catch (z3_exception & ex) {
            // convert all Z3 exceptions into tactic exceptions
            TRACE("linxi_subpaving",
                tout << "exception: " << ex.msg() << "\n";
            );
            throw tactic_exception(ex.msg());
        }
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m();
        dealloc(m_imp);
        m_imp = alloc(imp, m, m_params);
    }

};


tactic * mk_subpaving_tactic_core(ast_manager & m, params_ref const & p) {
    return alloc(subpaving_tactic, m, p);
}

void linxi_trace() {
    // enable_trace("subpaving_tactic");
    // enable_trace("subpaving_stats");
    // enable_trace("subpaving_main");
    // enable_trace("subpaving_init");
    // enable_trace("subpaving_propagate");
    // enable_trace("subpaving_relevant_bound");
    // enable_trace("subpaving_mk_bound");
    
    // enable_trace("propagate_clause");
    // enable_trace("propagate_monomial");
    // enable_trace("propagate_polynomial");
    // enable_trace("interval_xn_eq_y");
    // enable_trace("arith");
    // enable_trace("som");
    // enable_trace("poly_rewriter");
    // enable_trace("rewriter");

    enable_trace("linxi_subpaving");
}

tactic * mk_subpaving_tactic(ast_manager & m, params_ref const & p) {
    
    // linxi_trace();

    params_ref simp_p  = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("expand_power", true);
    simp_p.set_uint("max_power", UINT_MAX);
    simp_p.set_bool("som", true);
    simp_p.set_uint("som_blowup", UINT_MAX);

    simp_p.set_bool("elim_and", true);
    simp_p.set_bool("blast_distinct", true);
    
    params_ref simp2_p = p;
    simp2_p.set_bool("arith_lhs", true);
    simp2_p.set_bool("mul_to_power", true);

    return and_then(
                mk_elim_term_ite_tactic(m, p),
                mk_solve_eqs_tactic(m, p),
                using_params(mk_simplify_tactic(m, p), simp_p),
                mk_tseitin_cnf_core_tactic(m, p),
                using_params(mk_simplify_tactic(m, p), simp2_p),
                mk_subpaving_tactic_core(m, p)
            );
}


