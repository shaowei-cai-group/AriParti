/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving.cpp

Abstract:

    Subpaving for non-linear arithmetic.
    This is a wrapper for the different implementations
    of the subpaving module.
    This wrapper is the main interface between Z3 other modules and subpaving.
    Thus, it assumes that polynomials have precise integer coefficients, and
    bounds are rationals. If a particular implementation uses floats, then
    internally the bounds are approximated.
    
Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#include "math/subpaving/subpaving.h"
#include "math/subpaving/subpaving_types.h"
#include "math/subpaving/subpaving_mpq.h"

namespace subpaving {

    template<typename CTX>
    class context_wrapper : public context {
    protected:
        CTX m_ctx;
    public:
        context_wrapper(reslimit& lim, typename CTX::numeral_manager & m, params_ref const & p, small_object_allocator * a):m_ctx(lim, m, p, a) {}
        unsigned num_vars() const override { return m_ctx.num_vars(); }
        var mk_var(bool is_int) override { return m_ctx.mk_var(is_int); }
        var mk_bvar() override { return m_ctx.mk_bvar(); }
        bool is_int(var x) const override { return m_ctx.is_int(x); }
        var mk_monomial(unsigned sz, power const * pws) override { return m_ctx.mk_monomial(sz, pws); }
        void inc_ref(atom * a) override { m_ctx.inc_ref(reinterpret_cast<typename CTX::atom*>(a)); }
        void dec_ref(atom * a) override { m_ctx.dec_ref(reinterpret_cast<typename CTX::atom*>(a)); }
        void add_clause(unsigned sz, atom * const * atoms) override { m_ctx.add_clause(sz, reinterpret_cast<typename CTX::atom * const *>(atoms)); }
        void display_constraints(std::ostream & out, bool use_star) const override { m_ctx.display_constraints(out, use_star); }
        void set_task_ptr(task_info * p) override { m_ctx.set_task_ptr(p); }
        void set_display_proc(display_var_proc * p) override { m_ctx.set_display_proc(p); }
        void reset_statistics() override { m_ctx.reset_statistics(); }
        void collect_statistics(statistics & st) const override { m_ctx.collect_statistics(st); }
        void collect_param_descrs(param_descrs & r) override { m_ctx.collect_param_descrs(r); }
        void updt_params(params_ref const & p) override { m_ctx.updt_params(p); }
        lbool operator()() override { return m_ctx(); }
        void display_bounds(std::ostream & out) const override { m_ctx.display_bounds(out); }
    };

    class context_mpq_wrapper : public context_wrapper<context_mpq> {
        scoped_mpq        m_c;
        scoped_mpq_vector m_as;
    public:
        context_mpq_wrapper(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_mpq>(lim, m, p, a), 
            m_c(m), 
            m_as(m) 
        {}

        unsynch_mpq_manager & qm() const override { return m_ctx.nm(); }

        var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) override {
            m_as.reserve(sz);
            for (unsigned i = 0; i < sz; i++) {
                m_ctx.nm().set(m_as[i], as[i]);
            }
            m_ctx.nm().set(m_c, c);
            return m_ctx.mk_sum(m_c, sz, m_as.data(), xs);
        }
        atom * mk_bool_atom(var x, bool neg) override {
            return reinterpret_cast<atom*>(m_ctx.mk_bool_atom(x, neg)); 
        }
        atom * mk_eq_atom(var x, mpq const & k, bool neg) override {
            return reinterpret_cast<atom*>(m_ctx.mk_eq_atom(x, k, neg)); 
        }
        atom * mk_ineq_atom(var x, mpq const & k, bool lower, bool open) override {
            return reinterpret_cast<atom*>(m_ctx.mk_ineq_atom(x, k, lower, open)); 
        }
    };

    context * mk_mpq_context(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpq_wrapper, lim, m, p, a);
    }

};
