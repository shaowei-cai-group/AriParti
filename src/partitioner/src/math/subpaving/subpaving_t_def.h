/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_t_def.h

Abstract:

    Subpaving template for non-linear arithmetic.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#pragma once

#include "math/subpaving/subpaving_t.h"
#include "math/interval/interval_def.h"
#include "util/buffer.h"
#include "util/z3_exception.h"
#include "util/common_msgs.h"
#include "util/gparams.h"
#include <memory>
#include <thread>

namespace subpaving {

/**
   \brief Auxiliary static method used to display a bound specified by (x, k, lower, open).
*/
template<typename C>
void context_t<C>::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc, var x, numeral & k, bool lower, bool open) {
    if (lower) {
        out << nm.to_rational_string(k) << " <";
        if (!open)
            out << "=";
        out << " ";
        proc(out, x);
    }
    else {
        proc(out, x);
        out << " <";
        if (!open)
            out << "=";
        out << " " << nm.to_rational_string(k);
    }
}

template<typename C>
void context_t<C>::atom::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    context_t<C>::display(out, nm, proc, m_x, m_val, is_lower(), is_open());
}

template<typename C>
void context_t<C>::bound::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    context_t<C>::display(out, nm, proc, m_x, m_val, is_lower(), is_open());
}

template<typename C>
void context_t<C>::clause::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc) {
    for (unsigned i = 0; i < size(); i++) {
        if (i > 0)
            out << " or ";
        m_atoms[i]->display(out, nm, proc);
    }
}

template<typename C>
context_t<C>::node::node(context_t & s, unsigned id, bool_vector &is_bool):
    m_bm(s.bm()),
    m_bvm(s.bvm())
    {
    m_id              = id;
    m_depth           = 0;
    unsigned num_vars = s.num_vars();
    m_conflict        = null_var;
    m_trail           = nullptr;
    m_parent          = nullptr;
    m_first_child     = nullptr;
    m_next_sibling    = nullptr;
    m_prev            = nullptr;
    m_next            = nullptr;
    bm().mk(m_lowers);
    bm().mk(m_uppers);
    for (unsigned i = 0; i < num_vars; i++) {
        bm().push_back(m_lowers, nullptr);
        bm().push_back(m_uppers, nullptr);
        if (is_bool[i])
            bvm().push_back(m_bvalue, bvalue_kind::b_undef);
        else
            bvm().push_back(m_bvalue, bvalue_kind::b_arith);
    }
}

template<typename C>
context_t<C>::node::node(node * parent, unsigned id):
    m_bm(parent->m_bm),
    m_bvm(parent->m_bvm)
{    
    m_id             = id;
    m_depth          = parent->depth() + 1;
    bm().copy(parent->m_lowers, m_lowers);
    bm().copy(parent->m_uppers, m_uppers);
    bvm().copy(parent->m_bvalue, m_bvalue);
    m_conflict       = parent->m_conflict;
    m_trail          = parent->m_trail;
    m_parent         = parent;
    m_first_child    = nullptr;
    m_next_sibling   = parent->m_first_child;
    m_prev           = nullptr;
    m_next           = nullptr;
    parent->m_first_child = this;

    m_up_atoms.append(parent->m_up_atoms.size(), parent->m_up_atoms.data());
}

/**
   \brief Add a new bound b at this node.
*/
template<typename C>
void context_t<C>::node::push(bound * b) {
    SASSERT(b->prev() == m_trail);
    m_trail = b;
    var x = b->x();
    bvalue_kind bk = bvm().get(m_bvalue, x);
    if (bk == bvalue_kind::b_arith) {
        if (b->is_lower()) {
            bm().set(m_lowers, b->x(), b);
            SASSERT(lower(b->x()) == b);
        }
        else {
            bm().set(m_uppers, b->x(), b);
            SASSERT(upper(b->x()) == b);
        }
    }
    else {
        bvalue_kind nbk = b->is_lower() ? b_false : b_true;
        if (bk == bvalue_kind::b_undef) {
            bvm().set(m_bvalue, x, nbk);
        }
        else {
            if (nbk != bk)
                bvm().set(m_bvalue, x, b_conflict);
        }
    }
}

/**
    \brief Return the most recent variable that was used for splitting on node n.
*/
template<typename C>
var context_t<C>::splitting_var(node * n) const {
    if (n == m_root)
        return null_var;
    bound * b = n->trail_stack();
    while (b != nullptr) {
        if (b->jst().is_axiom())
            return b->x();
        b = b->prev();
    }
    UNREACHABLE();
    return null_var;
}

template<typename C>
context_t<C>::monomial::monomial(unsigned sz, power const * pws):
    definition(constraint::MONOMIAL),
    m_size(sz) {
    std::uninitialized_copy(pws, pws + sz, m_powers);
    std::sort(m_powers, m_powers+sz, typename power::lt_proc());
    DEBUG_CODE({
            for (unsigned i = 0; i < sz; i ++) {
                SASSERT(i == 0 || x(i) > x(i-1));
                SASSERT(degree(i) > 0);
            }});
}

template<typename C>
void context_t<C>::monomial::display(std::ostream & out, display_var_proc const & proc, bool use_star) const {
    SASSERT(m_size > 0);
    for (unsigned i = 0; i < m_size; i++) {
        if (i > 0) {
            if (use_star)
                out << "*";
            else
                out << " ";
        }
        proc(out, x(i));
        if (degree(i) > 1)
            out << "^" << degree(i);
    }
}

template<typename C>
void context_t<C>::polynomial::display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc, bool use_star) const {
    bool first = true;
    if (!nm.is_zero(m_c)) {
        out << nm.to_rational_string(m_c);
        first = false;
    }

    for (unsigned i = 0; i < m_size; i++) {
        if (first)
            first = false;
        else
            out << " + ";
        if (!nm.is_one(a(i))) {
            out << nm.to_rational_string(a(i));
            if (use_star)
                out << "*";
            else
                out << " ";
        }
        proc(out, x(i));
    }
}

template<typename C>
context_t<C>::context_t(reslimit& lim, C const & c, params_ref const & p, small_object_allocator * a):
    m_limit(lim),
    m_c(c),
    m_own_allocator(a == nullptr),
    m_allocator(a == nullptr ? alloc(small_object_allocator, "subpaving") : a),
    m_bm(*this, *m_allocator),
    m_bvm(*this, *m_allocator),
    m_init(false),
    m_best_var_info(nm()),
    m_curr_var_info(nm()),
    m_im(lim, interval_config(m_c.m())),
    m_num_buffer(nm())
{
    m_arith_failed  = false;
    m_timestamp     = 0;
    m_root          = nullptr;
    m_leaf_head     = nullptr;
    m_leaf_tail     = nullptr;
    m_conflict      = null_var;
    m_qhead         = 0;
    m_display_proc  = &m_default_display_proc;

    m_num_nodes     = 0;
    updt_params(p);
    reset_statistics();
}

template<typename C>
context_t<C>::~context_t() {
    nm().del(m_epsilon);
    nm().del(m_max_bound);
    nm().del(m_split_delta);
    nm().del(m_unbounded_penalty);
    nm().del(m_unbounded_penalty_sq);
    nm().del(m_minus_max_bound);
    nm().del(m_nth_root_prec);
    nm().del(m_max_denominator);
    nm().del(m_adjust_denominator);
    nm().del(m_tmp1);
    nm().del(m_tmp2);
    nm().del(m_tmp3);
    nm().del(m_ztmp1);
    del(m_i_tmp1);
    del(m_i_tmp2);
    del(m_i_tmp3);
    del_nodes();
    del_unit_clauses();
    del_clauses();
    del_definitions();
    if (m_own_allocator)
        dealloc(m_allocator);
}

template<typename C>
void context_t<C>::checkpoint() {
    if (!m_limit.inc())
        throw default_exception(Z3_CANCELED_MSG);
    if (memory::get_allocation_size() > m_max_memory)
        throw default_exception(Z3_MAX_MEMORY_MSG);
}

template<typename C>
void context_t<C>::del(interval & a) {
    nm().del(a.m_l_val);
    nm().del(a.m_u_val);
}

template<typename C>
void context_t<C>::updt_params(params_ref const & p) {
    unsigned epsilon = p.get_uint("epsilon", 20);
    if (epsilon != 0) {
        nm().set(m_epsilon, static_cast<int>(epsilon));
        nm().inv(m_epsilon);
        m_zero_epsilon = false;
    }
    else {
        nm().reset(m_epsilon);
        m_zero_epsilon = true;
    }
    
    unsigned max_power = p.get_uint("max_bound", 10);
    nm().set(m_max_bound, 10);
    nm().power(m_max_bound, max_power, m_max_bound);
    nm().set(m_minus_max_bound, m_max_bound);
    nm().neg(m_minus_max_bound);

    // max denominator 10^20
    nm().set(m_max_denominator, 10);
    nm().power(m_max_denominator, 20, m_max_denominator);

    // denominator after adjust 10^15
    nm().set(m_adjust_denominator, 10);
    nm().power(m_adjust_denominator, 15, m_adjust_denominator);
    

    m_max_depth = p.get_uint("max_depth", 128);
    //#linxi
    // m_max_nodes = p.get_uint("max_nodes", 8192);
    m_max_nodes = p.get_uint("max_nodes", 32);

    m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));

    unsigned prec = p.get_uint("nth_root_precision", 8192);
    if (prec == 0)
        prec = 1;
    nm().set(m_nth_root_prec, static_cast<int>(prec));
    nm().inv(m_nth_root_prec);
}

template<typename C>
void context_t<C>::collect_param_descrs(param_descrs & d) {
    d.insert("max_nodes", CPK_UINT, "(default: 8192) maximum number of nodes in the subpaving tree.");
    d.insert("max_depth", CPK_UINT, "(default: 128) maximum depth of the subpaving tree.");
    d.insert("epsilon", CPK_UINT, "(default: 20) value k s.t. a new lower (upper) bound for x is propagated only new-lower(x) > lower(k) + 1/k * max(min(upper(x) - lower(x), |lower|), 1) (new-upper(x) < upper(x) - 1/k * max(min(upper(x) - lower(x), |lower|), 1)). If k = 0, then this restriction is ignored.");
    d.insert("max_bound", CPK_UINT, "(default 10) value k s.t. a new upper (lower) bound for x is propagated only if upper(x) > -10^k or lower(x) = -oo (lower(x) < 10^k or upper(x) = oo)");
    d.insert("nth_root_precision", CPK_UINT, "(default 8192) value k s.t. 1/k is the precision for computing the nth root in the subpaving module.");
}

template<typename C>
void context_t<C>::display_params(std::ostream & out) const {
    out << "max_nodes  " << m_max_nodes << "\n";
    out << "max_depth  " << m_max_depth << "\n";
    out << "epsilon    " << nm().to_rational_string(m_epsilon) << "\n";
    out << "max_bound  " << nm().to_rational_string(m_max_bound) << "\n";
    out << "max_memory " << m_max_memory << "\n";
}

template<typename C>
typename context_t<C>::bound * context_t<C>::mk_bvar_bound(var x, bool neg, node * n, justification jst) {
    SASSERT(!inconsistent(n));
    ++m_num_mk_bounds;
    void * mem = allocator().allocate(sizeof(bound));
    bound * r  = new (mem) bound();
    r->m_x         = x;
    r->m_lower     = neg;
    r->m_mark      = false;
    r->m_timestamp = m_timestamp;
    r->m_prev      = n->trail_stack();
    r->m_jst       = jst;
    n->push(r);
    TRACE("subpaving_mk_bound", tout << "mk_bound: "; display(tout, r); tout << "\ntimestamp: " << r->m_timestamp << "\n";);
    if (conflicting_bvar_bounds(x, n)) {
        TRACE("subpaving_mk_bound", tout << "conflict\n"; display_bounds(tout, n););
        set_conflict(x, n);
    }
    ++m_timestamp;
    if (m_timestamp == UINT64_MAX)
        throw subpaving::exception(); // subpaving failed.
    return r;
}

template<typename C>
void context_t<C>::adjust_integer_bound(numeral const &val, numeral &result, bool lower, bool &open) {
    // adjust integer bound
    if (!nm().is_int(val)) {
        open = false; // performing ceil/floor
        if (lower)
            nm().ceil(val, result);
        else
            nm().floor(val, result);
    }
    else {
        nm().set(result, val);
    }
    if (open) {
        open = false;
        if (lower)  {
            C::round_to_minus_inf(nm());
            nm().inc(result);
        }
        else {
            C::round_to_plus_inf(nm());
            nm().dec(result);
        }
    }
}

template<typename C>
void context_t<C>::adjust_relaxed_bound(numeral const &val, numeral &result, bool lower, bool &open) {
    // adjust integer bound
    if (!nm().is_int(val)) {
        open = true; // performing ceil/floor
        if (lower)
            nm().floor(val, result);
        else
            nm().ceil(val, result);
    }
    else
        nm().set(result, val);
}

template<typename C>
typename context_t<C>::bound * context_t<C>::mk_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst) {
    SASSERT(!inconsistent(n));
    m_num_mk_bounds++;
    void * mem = allocator().allocate(sizeof(bound));
    bound * r  = new (mem) bound();
    r->m_x         = x;
    nm().set(r->m_val, val);
    r->m_lower     = lower;
    r->m_open      = open;
    r->m_mark      = false;
    r->m_timestamp = m_timestamp;
    r->m_prev      = n->trail_stack();
    r->m_jst       = jst;
    n->push(r);
    TRACE("subpaving_mk_bound", tout << "mk_bound: "; display(tout, r); tout << "\ntimestamp: " << r->m_timestamp << "\n";);
    if (conflicting_bounds(x, n)) {
        TRACE("subpaving_mk_bound", tout << "conflict\n"; display_bounds(tout, n););
        set_conflict(x, n);
    }
    m_timestamp++;
    if (m_timestamp == UINT64_MAX)
        throw subpaving::exception(); // subpaving failed.
    return r;
}
template<typename C>
bool context_t<C>::improve_bvar_bound(var x, bool neg, node * n) {
    bvalue_kind bk = n->bvalue(x);
    bvalue_kind nbk = neg ? b_false : b_true;
    if (bk == bvalue_kind::b_undef)
        return true;
    else if (nbk != bk)
        return true;
    return false;
}

template<typename C>
void context_t<C>::propagate_bvar_bound(var x, bool neg, node * n, justification jst) {
    if (!improve_bvar_bound(x, neg, n))
        return;
    TRACE("linxi_subpaving", 
        tout << "propagate_bvar_bound: " << x << ", neg: " << neg << "\n";
    );
    bound * b = mk_bvar_bound(x, neg, n, jst);
    m_queue.push_back(b);
}

template<typename C>
void context_t<C>::propagate_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst) {
    numeral & nval = m_tmp3;
    normalize_bound(x, val, nval, lower, open);
    if (!improve_bound(x, nval, lower, open, n))
        return;
    bound * b = mk_bound(x, nval, lower, open, n, jst);
    m_queue.push_back(b);
    SASSERT(!lower || n->lower(x) == b);
    SASSERT(lower  || n->upper(x) == b);
    SASSERT(is_int(x) || !lower || nm().eq(n->lower(x)->value(), val));
    SASSERT(is_int(x) || lower  || nm().eq(n->upper(x)->value(), val));
    SASSERT(open || !nm().is_int(val) || !lower || nm().eq(n->lower(x)->value(), val));
    SASSERT(open || !nm().is_int(val) || lower  || nm().eq(n->upper(x)->value(), val));
    SASSERT(!lower || nm().ge(n->lower(x)->value(), val));
    SASSERT(lower  || nm().le(n->upper(x)->value(), val));
}

template<typename C>
void context_t<C>::del_bound(bound * b) {
    nm().del(b->m_val);
    b->~bound();
    allocator().deallocate(sizeof(bound), b);
}

template<typename C>
void context_t<C>::display(std::ostream & out, var x) const {
    if (x == null_var)
        out << "[null]";
    else
        (*m_display_proc)(out, x);
}

template<typename C>
void context_t<C>::display(std::ostream & out, bound * b) const {
    b->display(out, nm(), *m_display_proc);
}

template<typename C>
void context_t<C>::display(std::ostream & out, atom * a) const {
    a->display(out, nm(), *m_display_proc);
}

template<typename C>
void context_t<C>::display_definition(std::ostream & out, definition const * d, bool use_star) const {
    switch (d->get_kind()) {
    case constraint::MONOMIAL:
        static_cast<monomial const *>(d)->display(out, *m_display_proc, use_star);
        break;
    case constraint::POLYNOMIAL:
        static_cast<polynomial const *>(d)->display(out, nm(), *m_display_proc, use_star);
        break;
    default:
        UNREACHABLE();
    };
}

template<typename C>
void context_t<C>::display(std::ostream & out, constraint * c, bool use_star) const {
    if (c->get_kind() == constraint::CLAUSE)
        static_cast<clause*>(c)->display(out, nm(), *m_display_proc);
    else
        display_definition(out, static_cast<definition*>(c), use_star);
}

template<typename C>
void context_t<C>::display_bounds(std::ostream & out, node * n) const {
    unsigned num = num_vars();
    for (unsigned x = 0; x < num; x++) {
        bound * l = n->lower(x);
        bound * u = n->upper(x);
        if (l != nullptr) {
            display(out, l);
            out << " ";
        }
        if (u != nullptr) {
            display(out, u);
        }
        if (l != nullptr || u != nullptr)
            out << "\n";
    }
}

/**
   \brief Return true if all variables in m are integer.
*/
template<typename C>
bool context_t<C>::is_int(monomial const * m) const {
    for (unsigned i = 0; i < m->size(); i++) {
        if (is_int(m->x(i)))
            return true;
    }
    return false;
}

/**
   \brief Return true if all variables in p are integer, and all coefficients in p are integer.
*/
template<typename C>
bool context_t<C>::is_int(polynomial const * p) const {
    for (unsigned i = 0; i < p->size(); i++) {
        if (!is_int(p->x(i)) || !nm().is_int(p->a(i))) {
            TRACE("subpaving_is_int", tout << "polynomial is not integer due to monomial at i: " << i << "\n"; tout.flush();
                  display(tout, p->x(i)); tout << " "; nm().display(tout, p->a(i)); tout << "\n";);
            return false;
        }
    }
    return nm().is_int(p->c());
}

template<typename C>
var context_t<C>::mk_var(bool is_int) {
    var r = static_cast<var>(m_is_int.size());
    m_is_int.push_back(is_int);
    m_is_bool.push_back(false);
    m_defs.push_back(0);
    m_wlist.push_back(watch_list());
    return r;
}

template<typename C>
var context_t<C>::mk_bvar() {
    var r = static_cast<var>(m_is_int.size());
    m_is_int.push_back(false);
    m_is_bool.push_back(true);
    m_defs.push_back(0);
    m_wlist.push_back(watch_list());
    return r;
}

template<typename C>
void context_t<C>::del_monomial(monomial * m) {
    unsigned mem_sz = monomial::get_obj_size(m->size());
    m->~monomial();
    allocator().deallocate(mem_sz, m);
}

template<typename C>
var context_t<C>::mk_monomial(unsigned sz, power const * pws) {
    SASSERT(sz > 0);
    unsigned mem_sz  = monomial::get_obj_size(sz);
    void * mem       = allocator().allocate(mem_sz);
    monomial * r     = new (mem) monomial(sz, pws);
    var new_var      = mk_var(is_int(r));
    m_defs[new_var]  = r;
    for (unsigned i = 0; i < sz; i++) {
        var x = pws[i].x();
        m_wlist[x].push_back(watched(new_var));
    }
    return new_var;
}

template<typename C>
void context_t<C>::del_sum(polynomial * p) {
    unsigned sz = p->size();
    unsigned mem_sz = polynomial::get_obj_size(sz);
    for (unsigned i = 0; i < sz; i++) {
        nm().del(p->m_as[i]);
    }
    nm().del(p->m_c);
    p->~polynomial();
    allocator().deallocate(mem_sz, p);
}

template<typename C>
var context_t<C>::mk_sum(numeral const & c, unsigned sz, numeral const * as, var const * xs) {
    m_num_buffer.reserve(num_vars());
    for (unsigned i = 0; i < sz; i++) {
        SASSERT(xs[i] < num_vars());
        nm().set(m_num_buffer[xs[i]], as[i]);
    }
    unsigned mem_sz  = polynomial::get_obj_size(sz);
    void * mem       = allocator().allocate(mem_sz);
    polynomial * p   = new (mem) polynomial();
    p->m_size        = sz;
    nm().set(p->m_c, c);
    p->m_as          = reinterpret_cast<numeral*>(static_cast<char*>(mem) + sizeof(polynomial));
    p->m_xs          = reinterpret_cast<var*>(reinterpret_cast<char*>(p->m_as) + sizeof(numeral)*sz);
    memcpy(p->m_xs, xs, sizeof(var)*sz);
    std::sort(p->m_xs, p->m_xs+sz);
    for (unsigned i = 0; i < sz; i++) {
        numeral * curr = p->m_as + i;
        new (curr) numeral();
        var x = p->m_xs[i];
        nm().swap(m_num_buffer[x], *curr);
    }
    TRACE("subpaving_mk_sum", tout << "new variable is integer: " << is_int(p) << "\n";);
    var new_var      = mk_var(is_int(p));
    for (unsigned i = 0; i < sz; i++) {
        var x = p->m_xs[i];
        m_wlist[x].push_back(watched(new_var));
    }
    m_defs[new_var]  = p;
    return new_var;
}

template<typename C>
typename context_t<C>::atom * context_t<C>::mk_bool_atom(var x, bool neg) {
    void * mem = allocator().allocate(sizeof(atom));
    atom * r   = new (mem) atom();
    r->m_ref_count = 0;
    r->m_bool      = true;
    r->m_open      = false;
    r->m_lower     = neg;

    r->m_x         = x;
    return r;
}

template<typename C>
typename context_t<C>::atom * context_t<C>::mk_eq_atom(var x, numeral const & k, bool neg) {
    void * mem = allocator().allocate(sizeof(atom));
    atom * r   = new (mem) atom();
    r->m_ref_count = 0;
    r->m_bool      = true;
    r->m_open      = true;
    r->m_lower     = neg;

    r->m_x         = x;
    nm().set(r->m_val, k);
    return r;
}

template<typename C>
typename context_t<C>::atom * context_t<C>::mk_ineq_atom(var x, numeral const & k, bool lower, bool open) {
    void * mem = allocator().allocate(sizeof(atom));
    atom * r   = new (mem) atom();
    r->m_ref_count = 0;
    r->m_bool      = false;
    r->m_lower     = lower;
    r->m_open      = open;

    r->m_x         = x;
    nm().set(r->m_val, k);
    return r;
}

template<typename C>
void context_t<C>::inc_ref(atom * a) {
    TRACE("subpaving_ref_count", tout << "inc-ref: " << a << " " << a->m_ref_count << "\n";);
    if (a)
        a->m_ref_count++;
}

template<typename C>
void context_t<C>::dec_ref(atom * a) {
    if (a) {
        TRACE("subpaving_ref_count",
              tout << "dec-ref: " << a << " " << a->m_ref_count << "\n";
              a->display(tout, nm());
              tout << "\n";);
        SASSERT(a->m_ref_count > 0);
        a->m_ref_count--;
        if (a->m_ref_count == 0) {
            nm().del(a->m_val);
            a->~atom();
            allocator().deallocate(sizeof(atom), a);
        }
    }
}

template<typename C>
void context_t<C>::add_clause_core(unsigned sz, atom * const * atoms, bool lemma, bool watch) {
    SASSERT(lemma || watch);
    SASSERT(sz > 0);
    if (sz == 1) {
        add_unit_clause(atoms[0], true);
        return;
    }

    void * mem = allocator().allocate(clause::get_obj_size(sz));
    clause * c = new (mem) clause();
    c->m_size  = sz;
    for (unsigned i = 0; i < sz; i++) {
        inc_ref(atoms[i]);
        c->m_atoms[i] = atoms[i];
    }
    std::stable_sort(c->m_atoms, c->m_atoms + sz, typename atom::lt_var_proc());
    if (watch) {
        for (unsigned i = 0; i < sz; i++) {
            var x = c->m_atoms[i]->x();
            if (x != null_var && (i == 0 || x != c->m_atoms[i-1]->x()))
                m_wlist[x].push_back(watched(c));
        }
    }
    c->m_lemma   = lemma;
    c->m_num_jst = 0;
    c->m_watched = watch;
    if (!lemma) {
        m_clauses.push_back(c);
    }
    else if (watch) {
        m_lemmas.push_back(c);
    }
    TRACE("subpaving_clause", tout << "new clause:\n"; display(tout, c); tout << "\n";);
}

template<typename C>
void context_t<C>::del_clause(clause * c) {
    SASSERT(c->m_num_jst == 0); // We cannot delete a clause that is being used to justify some bound
    bool watch  = c->watched();
    var prev_x  = null_var;
    unsigned sz = c->size();
    for (unsigned i = 0; i < sz; i++) {
        var x = c->m_atoms[i]->x();
        if (watch) {
            if (x != prev_x)
                m_wlist[x].erase(watched(c));
            prev_x = x;
        }
        dec_ref((*c)[i]);
    }
    unsigned mem_sz = clause::get_obj_size(sz);
    c->~clause();
    allocator().deallocate(mem_sz, c);
}

template<typename C>
void context_t<C>::add_unit_clause(atom * a, bool axiom) {
    TRACE("subpaving", a->display(tout, nm(), *m_display_proc); tout << "\n";);
    inc_ref(a);
    m_unit_clauses.push_back(TAG(atom*, a, axiom));
}

template<typename C>
typename context_t<C>::node * context_t<C>::mk_node(node * parent) {
    void * mem = allocator().allocate(sizeof(node));
    node * r;
    if (parent == nullptr)
        r = new (mem) node(*this, m_node_id_gen.mk(), m_is_bool);
    else
        r = new (mem) node(parent, m_node_id_gen.mk());
    
    if (parent == nullptr) {
        for (unsigned i = 0; i < m_var_key_num; ++i)
            r->key_rank().push_back(i);
    }
    else {
        // dynamic key rank
        unsigned pos = 0;
        for (unsigned i = 0; i < m_var_key_num; ++i) {
            r->key_rank().push_back(parent->key_rank()[i]);
            if (i > 0 && pos == 0 && parent->key_rank()[i - 1] < parent->key_rank()[i])
                pos = i;
        }
        if (pos == 0) {
            for (unsigned i = 0; i < m_var_key_num; ++i)
                r->key_rank()[i] = i;
        }
        else {
            std::swap(r->key_rank()[pos - 1], r->key_rank()[pos]);
        }
        
        // static key rank
        // for (unsigned i = 0; i < m_var_key_num; ++i)
        //     r->key_rank().push_back(i);
    }

    // Add node in the leaf dlist
    push_front(r);
    m_num_nodes++;
    m_nodes.push_back(r);
    m_nodes_state.push_back(node_state::WAITING);
    return r;
}

template<typename C>
void context_t<C>::del_node(node * n) {
    SASSERT(n->first_child() == 0);

    SASSERT(m_num_nodes > 0);
    m_num_nodes--;

    // recycle id
    m_node_id_gen.recycle(n->id());

    // disconnect n from list of leaves.
    remove_from_leaf_dlist(n);

    // disconnect n from parent
    node * p = n->parent();
    bound * b = n->trail_stack();
    bound * b_old;
    if (p != nullptr) {
        node * c = p->first_child();
        if (c == n) {
            // n is the first child
            p->set_first_child(n->next_sibling());
        }
        else {
            SASSERT(c->next_sibling() != 0);
            while (c->next_sibling() != n) {
                c = c->next_sibling();
                SASSERT(c->next_sibling() != 0);
            }
            SASSERT(c->next_sibling() == n);
            c->set_next_sibling(n->next_sibling());
        }
        b_old = p->trail_stack();
    }
    else {
        b_old = nullptr;
    }
    while (b != b_old) {
        bound * old = b;
        b = b->prev();
        del_bound(old);
    }
    bm().del(n->uppers());
    bm().del(n->lowers());
    n->~node();
    allocator().deallocate(sizeof(node), n);
}

template<typename C>
void context_t<C>::del_nodes() {
    ptr_buffer<node> todo;
    if (m_root == nullptr)
        return;
    todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        node * c = n->first_child();
        if (c == nullptr) {
            del_node(n);
            todo.pop_back();
        }
        else {
            while (c != nullptr) {
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::push_front(node * n) {
    SASSERT(n->first_child() == 0);
    SASSERT(n->next() == 0);
    SASSERT(n->prev() == 0);
    n->set_next(m_leaf_head);
    if (m_leaf_head != nullptr) {
        SASSERT(m_leaf_head->prev() == 0);
        m_leaf_head->set_prev(n);
    }
    else {
        SASSERT(m_leaf_head == 0);
        m_leaf_tail = n;
    }
    m_leaf_head = n;
}

template<typename C>
void context_t<C>::push_back(node * n) {
    SASSERT(n->first_child() == 0);
    SASSERT(n->next() == 0);
    SASSERT(n->prev() == 0);
    n->set_prev(m_leaf_tail);
    if (m_leaf_tail != nullptr) {
        SASSERT(m_leaf_tail->next() == 0);
        m_leaf_tail->set_next(n);
    }
    else {
        SASSERT(m_leaf_tail == 0);
        m_leaf_head = n;
    }
    m_leaf_tail = n;
}

template<typename C>
void context_t<C>::reset_leaf_dlist() {
    // Remove all nodes from the lead doubly linked list
    node * n = m_leaf_head;
    while (n != nullptr) {
        node * next = n->next();
        n->set_next(nullptr);
        n->set_prev(nullptr);
        n = next;
    }
    m_leaf_head = nullptr;
    m_leaf_tail = nullptr;
}

template<typename C>
void context_t<C>::rebuild_leaf_dlist(node * n) {
    reset_leaf_dlist();
    // Reinsert all leaves in the leaf dlist.
    ptr_buffer<node, 1024> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        if (c == nullptr) {
            if (!n->inconsistent())
                push_front(n);
        }
        else  {
            while (c != nullptr) {
                SASSERT(c->parent() == n);
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::remove_from_leaf_dlist(node * n) {
    node * prev = n->prev();
    node * next = n->next();
    SASSERT(prev == 0 || prev != next);
    SASSERT(next == 0 || prev != next);
    SASSERT(prev != n); SASSERT(next != n);
    if (prev != nullptr) {
        SASSERT(m_leaf_head != n);
        prev->set_next(next);
        n->set_prev(nullptr);
    }
    else if (m_leaf_head == n) {
        m_leaf_head = next;
    }

    if (next != nullptr) {
        SASSERT(m_leaf_tail != n);
        next->set_prev(prev);
        n->set_next(nullptr);
    }
    else if (m_leaf_tail == n) {
        m_leaf_tail = prev;
    }
    SASSERT(n->prev() == 0 && n->next() == 0);
}

template<typename C>
void context_t<C>::collect_leaves(ptr_vector<node> & leaves) const {
    // Copy all leaves to the given vector.
    ptr_buffer<node, 1024> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        if (c == nullptr) {
            if (!n->inconsistent())
                leaves.push_back(n);
        }
        else  {
            while (c != nullptr) {
                SASSERT(c->parent() == n);
                todo.push_back(c);
                c = c->next_sibling();
            }
        }
    }
}

template<typename C>
void context_t<C>::del_unit_clauses() {
    unsigned sz = m_unit_clauses.size();
    for (unsigned i = 0; i < sz; i++)
        dec_ref(UNTAG(atom*, m_unit_clauses[i]));
    m_unit_clauses.reset();
}

template<typename C>
void context_t<C>::del_clauses(ptr_vector<clause> & cs) {
    unsigned sz = cs.size();
    for (unsigned i = 0; i < sz; i++) {
        del_clause(cs[i]);
    }
    cs.reset();
}

template<typename C>
void context_t<C>::del_clauses() {
    del_clauses(m_clauses);
    del_clauses(m_lemmas);
}

template<typename C>
void context_t<C>::del_definitions() {
    unsigned sz = num_vars();
    for (unsigned i = 0; i < sz; i++) {
        definition * d = m_defs[i];
        if (d == nullptr)
            continue;
        switch (d->get_kind()) {
        case constraint::MONOMIAL:
            del_monomial(static_cast<monomial*>(d));
            break;
        case constraint::POLYNOMIAL:
            del_sum(static_cast<polynomial*>(d));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
}

template<typename C>
void context_t<C>::display_constraints(std::ostream & out, bool use_star) const {
    // display definitions
    out << "definitions:\n";
    for (unsigned i = 0; i < num_vars(); i++) {
        if (is_definition(i)) {
            (*m_display_proc)(out, i);
            out << " = ";
            display_definition(out, m_defs[i], use_star);
            out << "\n";
        }
    }
    // display units
    out << "units:\n";
    for (unsigned i = 0; i < m_unit_clauses.size(); i++) {
        atom * a = UNTAG(atom*, m_unit_clauses[i]);
        a->display(out, nm(), *m_display_proc); out << "\n";
    }
    // display clauses
    out << "clauses:\n";
    for (unsigned i = 0; i < m_clauses.size(); i++) {
        m_clauses[i]->display(out, nm(), *m_display_proc); out << "\n";
    }
}

// -----------------------------------
//
// Propagation
//
// -----------------------------------

template<typename C>
void context_t<C>::set_conflict(var x, node * n) {
    m_num_conflicts++;
    n->set_conflict(x);
    // remove_from_leaf_dlist(n);
}

template<typename C>
bool context_t<C>::may_propagate(bound * b, constraint * c, node * n) {
    SASSERT(b != 0 && c != 0);
    TRACE("may_propagate_bug", display(tout, b); tout << " | "; display(tout, c); tout << "\nresult: " << (b->timestamp() > c->timestamp()) << ", " << b->timestamp() << ", " << c->timestamp() << "\n";);
    return b->timestamp() >= c->timestamp();
}

// Normalization for bounds (for integer and too large denominator)
template<typename C>
void context_t<C>::normalize_bound(var x, const numeral &val, numeral &result, bool lower, bool & open) {
    TRACE("linxi_subpaving",
        tout << "before normalize\n"
             << "x: " << x << ", val: ";
        nm().display(tout, val);
        tout << ", lower: " << lower
             << ", open: " << open << "\n";
    );
    if (is_int(x)) {
        // adjust integer bound
        adjust_integer_bound(val, result, lower, open);
    }
    else {
        mpz &deno = m_ztmp1;
        nm().get_denominator(val, deno);
        if (nm().gt(deno, m_max_denominator)) {
            numeral &nval = m_tmp1;
            nm().mul(m_adjust_denominator, val, nval);
            adjust_relaxed_bound(nval, result, lower, open);
            nm().div(result, m_adjust_denominator, result);
        }
        else {
            nm().set(result, val);
        }
    }
    
    TRACE("linxi_subpaving",
        tout << "after normalize\n"
             << "x: " << x << ", val: ";
        nm().display(tout, result);
        tout << ", lower: " << lower
             << ", open: " << open << "\n";
        tout << "(result, val) lt: " << nm().lt(result, val)
             << ", eq: " << nm().eq(result, val)
             << ", gt: " << nm().gt(result, val) << "\n";
    );
}

template<typename C>
void context_t<C>::normalize_bound(var x, numeral & val, bool lower, bool & open) {
    normalize_bound(x, val, val, lower, open);
}

template<typename C>
bool context_t<C>::relevant_new_bound(var x, numeral const & k, bool lower, bool open, node * n) {
    try {
        bound * curr_lower = n->lower(x);
        bound * curr_upper = n->upper(x);
        SASSERT(curr_lower == 0 || curr_lower->x() == x);
        SASSERT(curr_upper == 0 || curr_upper->x() == x);
        TRACE("subpaving_relevant_bound",
              display(tout, x); tout << " " << (lower ? ">" : "<") << (open ? "" : "=") << " "; nm().display(tout, k); tout << "\n";
              tout << "existing bounds:\n";
              if (curr_lower) { display(tout, curr_lower); tout << "\n"; }
              if (curr_upper) { display(tout, curr_upper); tout << "\n"; });
        if (lower) {
            // If new bound triggers a conflict, then it is relevant.
            if (curr_upper && (nm().gt(k, curr_upper->value()) || ((open || curr_upper->is_open()) && nm().eq(k, curr_upper->value())))) {
                TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
                return true;
            }
            // If m_epsilon is zero, then bound is relevant only if it improves existing bound.
            if (m_zero_epsilon && curr_lower != nullptr && (nm().lt(k, curr_lower->value()) || ((curr_lower->is_open() || !open) && nm().eq(k, curr_lower->value())))) {
                // new lower bound does not improve existing bound
                TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
                return false;
            }
            if (curr_upper == nullptr && nm().lt(m_max_bound, k)) {
                // new lower bound exceeds the :max-bound threshold
                TRACE("subpaving_relevant_bound", tout << "irrelevant because exceeds :max-bound threshold.\n";);
                return false;
            }
            if (!m_zero_epsilon && curr_lower != nullptr) {
                // check if:
                // new-lower > lower + m_epsilon * max(min(upper - lower, |lower|), 1)
                numeral & min       = m_tmp1;
                numeral & abs_lower = m_tmp2;
                nm().set(abs_lower, curr_lower->value());
                nm().abs(abs_lower);
                if (curr_upper != nullptr) {
                    nm().sub(curr_upper->value(), curr_lower->value(), min);
                    if (nm().lt(abs_lower, min))
                        nm().set(min, abs_lower);
                }
                else {
                    nm().set(min, abs_lower);
                }
                numeral & delta    = m_tmp3;
                nm().set(delta, 1);
                if (nm().gt(min, delta))
                    nm().set(delta, min);
                nm().mul(delta, m_epsilon, delta);
                nm().add(curr_lower->value(), delta, delta);
                TRACE("subpaving_relevant_bound_bug",
                      tout << "k: "; nm().display(tout, k);
                      tout << ", delta: "; nm().display(tout, delta); tout << "\n";
                      tout << "curr_lower: "; nm().display(tout, curr_lower->value());
                      tout << ", min: "; nm().display(tout, min); tout << "\n";);
                if (nm().le(k, delta)) {
                    TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound to at least ";
                          nm().display(tout, delta); tout << "\n";);
                    return false;
                }
            }
        }
        else {
            // If new bound triggers a conflict, then it is relevant.
            if (curr_lower && (nm().gt(curr_lower->value(), k) || ((open || curr_lower->is_open()) && nm().eq(k, curr_lower->value())))) {
                TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
                return true;
            }
            // If m_epsilon is zero, then bound is relevant only if it improves existing bound.
            if (m_zero_epsilon && curr_upper != nullptr && (nm().lt(curr_upper->value(), k) || ((curr_upper->is_open() || !open) && nm().eq(k, curr_upper->value())))) {
                // new upper bound does not improve existing bound
                TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
                return false;
            }
            if (curr_lower == nullptr && nm().lt(k, m_minus_max_bound)) {
                // new upper bound exceeds the -:max-bound threshold
                TRACE("subpaving_relevant_bound", tout << "irrelevant because exceeds -:max-bound threshold.\n";);
                return false;
            }
            if (!m_zero_epsilon && curr_upper != nullptr) {
                // check if:
                // new-upper < upper - m_epsilon * max(min(upper - lower, |upper|), 1)
                numeral & min       = m_tmp1;
                numeral & abs_upper = m_tmp2;
                nm().set(abs_upper, curr_upper->value());
                nm().abs(abs_upper);
                if (curr_lower != nullptr) {
                    nm().sub(curr_upper->value(), curr_lower->value(), min);
                    if (nm().lt(abs_upper, min))
                        nm().set(min, abs_upper);
                }
                else {
                    nm().set(min, abs_upper);
                }
                numeral & delta    = m_tmp3;
                nm().set(delta, 1);
                if (nm().gt(min, delta))
                    nm().set(delta, min);
                nm().mul(delta, m_epsilon, delta);
                nm().sub(curr_upper->value(), delta, delta);
                if (nm().ge(k, delta)) {
                    TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound to at least ";
                          nm().display(tout, delta); tout << "\n";);
                    return false;
                }
            }
        }
        TRACE("subpaving_relevant_bound", tout << "new bound is relevant\n";);
        return true;
    }
    catch (const typename C::exception &) {
        // arithmetic module failed.
        set_arith_failed();
        return false;
    }
}


template<typename C>
bool context_t<C>::improve_bound(var x, numeral const & k, bool lower, bool open, node * n) {
    bound * curr_lower = n->lower(x);
    bound * curr_upper = n->upper(x);
    SASSERT(curr_lower == 0 || curr_lower->x() == x);
    SASSERT(curr_upper == 0 || curr_upper->x() == x);
    TRACE("subpaving_relevant_bound",
        display(tout, x); tout << " " << (lower ? ">" : "<") << (open ? "" : "=") << " "; nm().display(tout, k); tout << "\n";
        tout << "existing bounds:\n";
        if (curr_lower) { display(tout, curr_lower); tout << "\n"; }
        if (curr_upper) { display(tout, curr_upper); tout << "\n"; }
    );
    if (lower) {
        // If new bound triggers a conflict, then it is relevant.
        if (curr_upper && (nm().gt(k, curr_upper->value()) || ((open || curr_upper->is_open()) && nm().eq(k, curr_upper->value())))) {
            TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
            return true;
        }
        // Bound is relevant only if it improves existing bound.
        if (curr_lower != nullptr && (nm().lt(k, curr_lower->value()) || ((curr_lower->is_open() || !open) && nm().eq(k, curr_lower->value())))) {
            // new lower bound does not improve existing bound
            TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
            return false;
        }
    }
    else {
        // If new bound triggers a conflict, then it is relevant.
        if (curr_lower && (nm().gt(curr_lower->value(), k) || ((open || curr_lower->is_open()) && nm().eq(k, curr_lower->value())))) {
            TRACE("subpaving_relevant_bound", tout << "relevant because triggers conflict.\n";);
            return true;
        }
        // Bound is relevant only if it improves existing bound.
        if (curr_upper != nullptr && (nm().lt(curr_upper->value(), k) || ((curr_upper->is_open() || !open) && nm().eq(k, curr_upper->value())))) {
            // new upper bound does not improve existing bound
            TRACE("subpaving_relevant_bound", tout << "irrelevant because does not improve existing bound.\n";);
            return false;
        }
    }
    TRACE("subpaving_relevant_bound", tout << "new bound is relevant\n";);
    return true;
}


template<typename C>
bool context_t<C>::is_zero(var x, node * n) const {
    // Return true if lower(x) == upper(x) == 0 at n
    bound * l = n->lower(x);
    bound * u = n->upper(x);
    return l != nullptr && u != nullptr && nm().is_zero(l->value()) && nm().is_zero(u->value()) && !l->is_open() && !u->is_open();
}

template<typename C>
bool context_t<C>::is_upper_zero(var x, node * n) const {
    // Return true if upper(x) is zero at node n
    bound * u = n->upper(x);
    return u != nullptr && nm().is_zero(u->value()) && !u->is_open();
}

template<typename C>
bool context_t<C>::conflicting_bvar_bounds(var x, node * n) const {
    // Return true if bvalue[x] == b_conflict
    return n->bvalue(x) == bvalue_kind::b_conflict;
}

template<typename C>
bool context_t<C>::conflicting_bounds(var x, node * n) const {
    // Return true if upper(x) < lower(x) at node n
    bound * l = n->lower(x);
    bound * u = n->upper(x);
    return l != nullptr && u != nullptr && (nm().lt(u->value(), l->value()) || ((l->is_open() || u->is_open()) && nm().eq(u->value(), l->value())));
}

/**
   \brief Return the truth value of the atom t in node n.

   The result may be l_true (True), l_false (False), or l_undef(Unknown).
*/
template<typename C>
lbool context_t<C>::value(atom * t, node * n) {
    var x = t->x();
    bvalue_kind bk = n->bvalue(x);
    if (t->m_bool) {
        if (t->m_open) {
            // equation
            if (is_int(x) && !nm().is_int(t->value())) {
                if (t->is_lower())
                    return l_true;
                return l_false;
            }
            bound * u = n->upper(x);
            bound * l = n->lower(x);
            if (u == nullptr && l == nullptr)
                return l_undef;
            if (u != nullptr && nm().eq(u->value(), t->value()) && 
                l != nullptr && nm().eq(l->value(), t->value())) {
                if (t->is_lower())
                    return l_false;
                else
                    return l_true;
            }
            if (t->is_lower()) {
                if (u != nullptr && (nm().lt(u->value(), t->value()) || (u->is_open() && nm().eq(u->value(), t->value()))))
                    return l_true;
                if (l != nullptr && (nm().gt(l->value(), t->value()) || (l->is_open() && nm().eq(l->value(), t->value()))))
                    return l_true;
                return l_undef;
            }
            else {
                if (u != nullptr && (nm().lt(u->value(), t->value()) || (u->is_open() && nm().eq(u->value(), t->value()))))
                    return l_false;
                if (l != nullptr && (nm().gt(l->value(), t->value()) || (l->is_open() && nm().eq(l->value(), t->value()))))
                    return l_false;
                return l_undef;
            }
        }
        else {
            SASSERT(bk != bvalue_kind::b_arith);
            if (bk == bvalue_kind::b_undef)
                return l_undef;
            // lower means neg
            bvalue_kind nbk = t->m_lower ? b_false : b_true;
            if (bk != nbk)
                return l_false;
            return l_true;
        }
    }
    else {
        SASSERT(bk == bvalue_kind::b_arith);
        bound * u = n->upper(x);
        bound * l = n->lower(x);
        if (u == nullptr && l == nullptr)
            return l_undef;
        else if (t->is_lower()) {
            if (u != nullptr && (nm().lt(u->value(), t->value()) || ((u->is_open() || t->is_open()) && nm().eq(u->value(), t->value()))))
                return l_false;
            else if (l != nullptr && (nm().gt(l->value(), t->value()) || ((l->is_open() || !t->is_open()) && nm().eq(l->value(), t->value()))))
                return l_true;
            else
                return l_undef;
        }
        else {
            if (l != nullptr && (nm().gt(l->value(), t->value()) || ((l->is_open() || t->is_open()) && nm().eq(l->value(), t->value()))))
                return l_false;
            else if (u != nullptr && (nm().lt(u->value(), t->value()) || ((u->is_open() || !t->is_open()) && nm().eq(u->value(), t->value()))))
                return l_true;
            else
                return l_undef;
        }
    }
}

template<typename C>
void context_t<C>::propagate_clause(clause * c, node * n) {
    TRACE("propagate_clause", tout << "propagate using:\n"; display(tout, c); tout << "\n";);
    m_num_visited++;
    c->set_visited(m_timestamp);
    unsigned sz = c->size();
    unsigned j  = UINT_MAX;
    for (unsigned i = 0; i < sz; i++) {
        atom * at = (*c)[i];
        TRACE("linxi_subpaving",
            tout << "l[" << i << "] = " << value(at, n) << "\n";
        );
        switch (value(at, n)) {
        case l_true:
            return; // clause was already satisfied at n
        case l_false:
            break;
        case l_undef:
            if (j != UINT_MAX)
                return; // clause has more than one unassigned literal
            j = i;
            break;
        }
    }
    if (j == UINT_MAX) {
        // Clause is in conflict, use first atom to trigger inconsistency
        j = 0;
    }
    else {
        n->up_atoms().push_back((*c)[j]);
    }
    atom * a = (*c)[j];
    TRACE("propagate_clause", tout << "propagating inequality: "; display(tout, a); tout << "\n";);

    if (a->m_bool) {
        if (a->m_open) {
            if (!a->m_lower) {
                propagate_bound(a->x(), a->value(), true, false, n, justification(c));
                if (inconsistent(n))
                    return;
                propagate_bound(a->x(), a->value(), false, false, n, justification(c));
            }
        }
        else
            propagate_bvar_bound(a->x(), a->is_lower(), n, justification(c));
    }
    else
        propagate_bound(a->x(), a->value(), a->is_lower(), a->is_open(), n, justification(c));
    // A clause can propagate only once.
    // So, we can safely set its timestamp again to avoid another useless visit.
    c->set_visited(m_timestamp);
}

template<typename C>
void context_t<C>::propagate_polynomial(var x, node * n, var y) {
    SASSERT(y != null_var);
    SASSERT(is_polynomial(x));
    TRACE("linxi_subpaving",
        tout << "propagate_polynomial:\n";
        tout << "x: "; display(tout, x); tout << "\n";
        tout << "y: "; display(tout, y); tout << "\n";
    );
    polynomial * p = get_polynomial(x);
    unsigned sz    = p->size();
    interval & r   = m_i_tmp1; r.set_mutable();
    interval & v   = m_i_tmp2;
    interval & av  = m_i_tmp3; av.set_mutable();
    if (x == y) {
        for (unsigned i = 0; i < sz; i++) {
            var z = p->x(i);
            v.set_constant(n, z);
            im().mul(p->a(i), v, av);
            if (i == 0)
                im().set(r, av);
            else
                im().add(r, av, r);
        }
        // r contains the deduced bounds for x == y
    }
    else {
        v.set_constant(n, x);
        numeral & a = m_tmp1;
        im().set(r, v);
        for (unsigned i = 0; i < sz; i++) {
            var z = p->x(i);
            if (z != y) {
                v.set_constant(n, z);
                im().mul(p->a(i), v, av);
                im().sub(r, av, r);
            }
            else {
                nm().set(a, p->a(i));
                TRACE("propagate_polynomial_bug", tout << "a: "; nm().display(tout, a); tout << "\n";);
            }
        }
        TRACE("propagate_polynomial_bug", tout << "r before mul 1/a: "; im().display(tout, r); tout << "\n";);
        im().div(r, a, r);
        TRACE("propagate_polynomial_bug", tout << "r after mul 1/a:  "; im().display(tout, r); tout << "\n";);
        // r contains the deduced bounds for y.
    }
    TRACE("linxi_subpaving",
        tout << "interval: ";
        im().display(tout, r);
        tout << "\n"
    );
    // r contains the deduced bounds for y.
    if (!r.m_l_inf) {
        if (relevant_new_bound(y, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(y, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
    }
    if (!r.m_u_inf) {
        if (relevant_new_bound(y, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(y, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
void context_t<C>::propagate_polynomial(var x, node * n) {
    TRACE("propagate_polynomial", tout << "propagate_polynomial: "; display(tout, x); tout << "\n";);
    TRACE("propagate_polynomial_detail", display_bounds(tout, n););
    SASSERT(is_polynomial(x));
    polynomial * p = get_polynomial(x);
    p->set_visited(m_timestamp);
    var unbounded_var = null_var;
    if (is_unbounded(x, n))
        unbounded_var = x;
    unsigned sz = p->size();
    for (unsigned i = 0; i < sz; i++) {
        var y = p->x(i);
        if (is_unbounded(y, n)) {
            if (unbounded_var != null_var)
                return; // no propagation is possible.
            unbounded_var = y;
        }
    }
    TRACE("propagate_polynomial", tout << "unbounded_var: "; display(tout, unbounded_var); tout << "\n";);

    if (unbounded_var != null_var) {
        propagate_polynomial(x, n, unbounded_var);
    }
    else {
        propagate_polynomial(x, n, x);
        for (unsigned i = 0; i < sz; i++) {
            if (inconsistent(n))
                return;
            propagate_polynomial(x, n, p->x(i));
        }
    }
}

template<typename C>
void context_t<C>::propagate_monomial(var x, node * n) {
    TRACE("propagate_monomial", tout << "propagate_monomial: "; display(tout, x); tout << "\n";);
    SASSERT(is_monomial(x));
    SASSERT(!inconsistent(n));
    monomial * m = get_monomial(x);
    m->set_visited(m_timestamp);
    bool found_unbounded = false;
    bool found_zero      = false;
    bool x_is_unbounded  = false;
    unsigned sz = m->size();
    for (unsigned i = 0; i < sz; i++) {
        var y = m->x(i);
        TRACE("linxi_subpaving",
            tout << "item " << i << ": "; display(tout, y);
            tout << ", found zero: " << found_zero << "\n";
        );
        if (is_zero(y, n)) {
            found_zero = true;
        }
        if (m->degree(i) % 2 == 0) {
            //#linxi found error here
            // if (is_upper_zero(y, n)) {
            //     found_zero = true;
            // }
            continue; // elements with even power always produce a lower bound
        }
        if (is_unbounded(y, n)) {
            found_unbounded = true;
        }
    }
    TRACE("propagate_monomial", tout << "found_zero: " << found_zero << ", found_unbounded: " << found_unbounded << "\n";);
    if (found_zero) {
        if (!is_zero(x, n)) {
            // x must be zero
            numeral & zero = m_tmp1;
            nm().set(zero, 0);
            propagate_bound(x, zero, true,  false, n, justification(x));
            if (inconsistent(n))
                return;
            propagate_bound(x, zero, false, false, n, justification(x));
        }
        // no need to downward propagation
        return;
    }
    x_is_unbounded = n->is_unbounded(x);
    if (!found_unbounded)
        propagate_monomial_upward(x, n);
    if (inconsistent(n))
        return;
    if (!x_is_unbounded) {
        unsigned bad_pos = UINT_MAX;
        interval & aux   = m_i_tmp1;
        for (unsigned i = 0; i < sz; i++) {
            aux.set_constant(n, m->x(i));
            if (im().contains_zero(aux)) {
                if (bad_pos != UINT_MAX)
                    return; // there is more than one position that contains zero, so downward propagation is not possible.
                bad_pos = i;
            }
        }
        TRACE("linxi_subpaving",
            tout << "bad pos: " << bad_pos << "\n";
        );
        if (bad_pos == UINT_MAX) {
            // we can use all variables for downward propagation.
            for (unsigned i = 0; i < sz; i++) {
                if (inconsistent(n))
                    return;
                propagate_monomial_downward(x, n, i);
            }
        }
        else {
            propagate_monomial_downward(x, n, bad_pos);
        }
    }
}

template<typename C>
void context_t<C>::propagate_monomial_upward(var x, node * n) {
    SASSERT(is_monomial(x));
    monomial * m = get_monomial(x);
    unsigned sz  = m->size();
    interval & r  = m_i_tmp1; r.set_mutable();
    interval & y  = m_i_tmp2;
    interval & yk = m_i_tmp3; yk.set_mutable();
    for (unsigned i = 0; i < sz; i++) {
        y.set_constant(n, m->x(i));
        im().power(y, m->degree(i), yk);
        if (i == 0)
            im().set(r, yk);
        else
            im().mul(r, yk, r);
    }
    TRACE("linxi_subpaving",
        tout << "interval: ";
        im().display(tout, r);
        tout << "\n"
    );
    // r contains the new bounds for x
    if (!r.m_l_inf) {
        if (relevant_new_bound(x, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(x, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
    }
    if (!r.m_u_inf) {
        if (relevant_new_bound(x, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(x, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
void context_t<C>::propagate_monomial_downward(var x, node * n, unsigned j) {
    TRACE("propagate_monomial", tout << "propagate_monomial_downward: "; display(tout, x); tout << ", j: " << j << "\n";
          display(tout, get_monomial(x)); tout << "\n";);
    SASSERT(is_monomial(x));
    monomial * m = get_monomial(x);
    SASSERT(j < m->size());
    unsigned sz = m->size();

    interval & r = m_i_tmp3;
    if (sz > 1) {
        interval & d  = m_i_tmp1; d.set_mutable();
        interval & y  = m_i_tmp2;
        interval & yk = m_i_tmp3; yk.set_mutable();
        bool first = true;
        for (unsigned i = 0; i < sz; i++) {
            if (i == j)
                continue;
            y.set_constant(n, m->x(i));
            im().power(y, m->degree(i), yk);
            if (first) {
                im().set(d, yk);
                first = false;
            }
            else {
                im().mul(d, yk, r);
                im().set(d, r);
            }
        }
        if (im().contains_zero(d)) {
            im().reset_lower(r);
            im().reset_upper(r);
        }
        else {
            interval& aux = m_i_tmp2;
            aux.set_constant(n, x);
            im().div(aux, d, r);
        }
    }
    else {
        SASSERT(sz == 1);
        SASSERT(j == 0);
        interval & aux  = m_i_tmp2;
        aux.set_constant(n, x);
        im().set(r, aux);
    }
    TRACE("linxi_subpaving",
        tout << "interval: ";
        im().display(tout, r);
        tout << "\n"
    );
    unsigned deg = m->degree(j);
    if (deg > 1) {
        if (deg % 2 == 0 && im().lower_is_neg(r))
            return; // If d is even, we can't take the nth-root when lower(r) is negative.
        if (deg > 2)
            return;
        im().xn_eq_y(r, deg, m_nth_root_prec, r);
    }
    var y = m->x(j);
    // r contains the new bounds for y
    if (!r.m_l_inf) {
        if (relevant_new_bound(y, r.m_l_val, true, r.m_l_open, n)) {
            propagate_bound(y, r.m_l_val, true, r.m_l_open, n, justification(x));
            if (inconsistent(n))
                return;
        }
        propagate_bound(y, r.m_l_val, true, r.m_l_open, n, justification(x));
        if (inconsistent(n))
            return;
    }
    if (!r.m_u_inf) {
        if (relevant_new_bound(y, r.m_u_val, false, r.m_u_open, n))
            propagate_bound(y, r.m_u_val, false, r.m_u_open, n, justification(x));
    }
}

template<typename C>
bool context_t<C>::most_recent(bound * b, node * n) const {
    var x = b->x();
    if (b->is_lower())
        return n->lower(x) == b;
    else
        return n->upper(x) == b;
}

template<typename C>
void context_t<C>::add_recent_bounds(node * n) {
    SASSERT(m_queue.empty());
    bound * old_b = n->parent_trail_stack();
    bound * b     = n->trail_stack();
    while (b != old_b) {
        if (most_recent(b, n)) {
            b->set_timestamp(m_timestamp);
            m_queue.push_back(b);
        }
        b = b->prev();
    }
}

template<typename C>
void context_t<C>::propagate_def(var x, node * n) {
    SASSERT(is_definition(x));
    m_num_visited++;
    definition * d = m_defs[x];
    switch (d->get_kind()) {
    case constraint::MONOMIAL:
        propagate_monomial(x, n);
        break;
    case constraint::POLYNOMIAL:
        propagate_polynomial(x, n);
        break;
    default:
        break;
    }
}

template<typename C>
void context_t<C>::propagate_bvar(node * n, bound * b) {
    var x = b->x();
    TRACE("subpaving_propagate", tout << "propagate: "; display(tout, b); tout << ", timestamp: " << b->timestamp() << "\n";);
    ++m_curr_propagate;
    typename watch_list::const_iterator it  = m_wlist[x].begin();
    typename watch_list::const_iterator end = m_wlist[x].end();
    for (; it != end; ++it) {
        if (inconsistent(n))
            return;
        watched const & w = *it;
        SASSERT(w.is_clause());
        try {
            clause * c = w.get_clause();
            propagate_clause(c, n);
        }
        catch (const typename C::exception &) {
            // arithmetic module failed, ignore constraint
            set_arith_failed();
        }
    }
}

template<typename C>
bool context_t<C>::is_latest_bound(node * n, var x, uint64_t ts) {    
    bound * curr_lower = n->lower(x);
    bound * curr_upper = n->upper(x);
    if (curr_lower != nullptr && curr_lower->timestamp() > ts)
        return false;
    if (curr_upper != nullptr && curr_upper->timestamp() > ts)
        return false;
    return true;
}

template<typename C>
void context_t<C>::propagate(node * n, bound * b) {
    var x = b->x();
    if (!is_latest_bound(n, x, b->timestamp()))
        return;
    TRACE("subpaving_propagate", tout << "propagate: "; display(tout, b); tout << ", timestamp: " << b->timestamp() << "\n";);
    ++m_curr_propagate;
    typename watch_list::const_iterator it  = m_wlist[x].begin();
    typename watch_list::const_iterator end = m_wlist[x].end();
    for (; it != end; ++it) {
        if (inconsistent(n))
            return;
        watched const & w = *it;
        try {
            if (w.is_clause()) {
                clause * c = w.get_clause();
                if (may_propagate(b, c, n)) {
                    propagate_clause(c, n);
                }
            }
            else {
                var y = w.get_var();
                definition * d = m_defs[y];
                if (may_propagate(b, d, n)) {
                    propagate_def(y, n);
                }
            }
        }
        catch (const typename C::exception &) {
            // arithmetic module failed, ignore constraint
            set_arith_failed();
        }
    }
    if (inconsistent(n))
        return;
    if (is_definition(x)) {
        definition * d = m_defs[x];
        if (may_propagate(b, d, n)) {
            propagate_def(x, n);
        }
    }
}

template<typename C>
void context_t<C>::propagate(node * n) {
    m_curr_propagate = 0;
    unsigned prop_start = static_cast<unsigned>(std::time(nullptr));
    while (!inconsistent(n) && m_qhead < m_queue.size()
            && m_curr_propagate < m_max_propagate
            && static_cast<unsigned>(std::time(nullptr)) - prop_start <= 60) {
        checkpoint();
        bound * b = m_queue[m_qhead];
        m_qhead++;
        SASSERT(is_bound_of(b, n));
        if (m_is_bool[b->x()])
            propagate_bvar(n, b);
        else
            propagate(n, b);
    }
    TRACE("linxi_subpaving", tout << "node #" << n->id() << " after propagation\n";
            display_bounds(tout, n););
    m_queue.reset();
    m_qhead = 0;
}

template<typename C>
void context_t<C>::propagate_all_definitions(node * n) {
    unsigned num = num_vars();
    for (unsigned x = 0; x < num; x++) {
        if (inconsistent(n))
            break;
        if (is_definition(x))
            propagate_def(x, n);
    }
}

// -----------------------------------
//
// Main
//
// -----------------------------------

template<typename C>
void context_t<C>::assert_units(node * n) {
    typename ptr_vector<atom>::const_iterator it  = m_unit_clauses.begin();
    typename ptr_vector<atom>::const_iterator end = m_unit_clauses.end();
    for (; it != end; ++it) {
        checkpoint();
        atom * a = UNTAG(atom *, *it);
        bool axiom = GET_TAG(*it) != 0;
        TRACE("subpaving_init", tout << "asserting: "; display(tout, a); tout << ", axiom: " << axiom << "\n";);
        if (a->x() == null_var)
            continue;
        if (a->m_bool) {
            if (a->m_open) {
                // eq-TBD
                if (a->m_lower) {
                    UNREACHABLE();
                }
                else {
                    propagate_bound(a->x(), a->value(), true, false, n, justification(axiom));
                    if (inconsistent(n))
                        return;
                    propagate_bound(a->x(), a->value(), false, false, n, justification(axiom));
                }
            }
            else
                propagate_bvar_bound(a->x(), a->is_lower(), n, justification(axiom));
        }
        else {
            propagate_bound(a->x(), a->value(), a->is_lower(), a->is_open(), n, justification(axiom));
        }
        if (inconsistent(n))
            break;
    }
    TRACE("subpaving_init", tout << "bounds after init\n"; display_bounds(tout, n););
}

template<typename C>
void context_t<C>::write_line_to_master(const std::string & data) {
    m_curr_line_time = static_cast<unsigned>(std::time(nullptr) - m_start_time);
    m_write_pipe << m_curr_line_time << " " << data << std::endl;
}

template<typename C>
void context_t<C>::write_ss_line_to_master() {
    write_line_to_master(m_temp_stringstream.str());
    m_temp_stringstream.str("");
    m_temp_stringstream.clear();
}

template<typename C>
void context_t<C>::write_debug_line_to_master(const std::string & data) {
    m_curr_line_time = static_cast<unsigned>(std::time(nullptr) - m_start_time);
    m_write_pipe << m_curr_line_time << " debug-info " << data << std::endl;
}

template<typename C>
bool context_t<C>::read_line_from_master(std::string & line) {
    if (std::getline(m_read_pipe, line)) {
        return true;
    }
    return false;
}

template<typename C>
void context_t<C>::init_communication() {
    m_read_pipe.open(m_output_dir + "/master-to-partitioner");
    m_write_pipe.open(m_output_dir + "/partitioner-to-master");
    if (m_read_pipe.eof())
        m_read_pipe.clear();
    read_parse_line();
}

template<typename C>
void context_t<C>::init_partition() {
    m_init = true;
    m_max_propagate = m_is_int.size();

    if (m_max_propagate > 1024)
        m_max_propagate = 1024;
    else if (m_max_propagate < 256u)
        m_max_propagate = 256u;
    
    m_max_prop_time = 60; // second

    m_ptask->reset();
    m_var_occs.resize(num_vars());
    m_var_max_deg.resize(num_vars());
    m_var_split_cnt.resize(num_vars(), 0);
    
    m_alive_task_num = 0;
    m_var_key_num = 5;
    m_unconvert_head = 0;

    const params_ref &p = gparams::get_ref();
    m_output_dir = p.get_str("output_dir", "ERROR");
    m_max_running_tasks = p.get_uint("partition_max_running_tasks", 32);
    m_max_alive_tasks = static_cast<unsigned>(m_max_running_tasks * 1.5);
    nm().set(m_split_delta, 128);
    nm().set(m_unbounded_penalty, 1024);
    nm().set(m_unbounded_penalty_sq, 1024 * 1024);
    init_communication();
}

template<typename C>
void context_t<C>::init() {
    SASSERT(m_root       == 0);
    SASSERT(m_leaf_head  == 0);
    SASSERT(m_leaf_tail  == 0);
    
    m_timestamp = 0;
    m_root      = mk_node();
    SASSERT(m_leaf_head == m_root);
    SASSERT(m_leaf_tail == m_root);
    TRACE("subpaving_init", display_constraints(tout););
    TRACE("linxi_subpaving", 
        tout << "init:\n";
        display_constraints(tout);
    );
    assert_units(m_root);
    propagate_all_definitions(m_root);
    TRACE("subpaving_init", tout << "root bounds after propagation\n"; display_bounds(tout, m_root););
    SASSERT(check_invariant());
}

template<typename C>
lit context_t<C>::convert_atom_to_lit(atom * a) {
    lit l;
    l.m_x = a->m_x;
    if (a->m_bool) {
        l.m_bool = true;
        l.m_lower = a->m_lower;
        if (a->m_open) {
            l.m_open = true;
            l.m_int = m_is_int[a->m_x];
            l.m_val = &a->m_val;
        }
        else {
            l.m_open = false;
        }
    }
    else {
        l.m_bool = false;
        l.m_int = m_is_int[a->m_x];
        l.m_lower = a->m_lower;
        l.m_open = a->m_open;
        l.m_val = &a->m_val;
    }
    return l;
}

template<typename C>
void context_t<C>::convert_node_to_task(node * n) {
    task_info & task = *m_ptask;
    SASSERT(task.m_node_id == UINT32_MAX);

    task.m_node_id = n->id();
    task.m_depth = n->depth();
    vector<lit> temp_units;
    for (unsigned i = 0, isz = m_clauses.size(); i < isz; ++i) {
        clause * cla = m_clauses[i];
        m_temp_atom_buffer.reset();
        bool skippable = false;
        for (unsigned j = 0, jsz = cla->m_size; j < jsz; ++j) {
            atom * a = (*cla)[j];
            lbool res = value(a, n);
            TRACE("linxi_subpaving",
                tout << "atom: ";
                display(tout, a);
                tout << "\n";
                tout << "bool: " << a->is_bool() << "\n";
                tout << "open: " << a->is_open() << "\n";
                tout << "lower: " << a->is_lower() << "\n";
                tout << "res: " << res << "\n";
            );
            if (res == l_true) {
                skippable = true;
                break;
            }
            else if (res == l_false) {
                continue;
            }
            else {
                m_temp_atom_buffer.push_back(a);
            }
        }
        if (skippable)
            continue;
        ++task.m_undef_clause_num;
        task.m_undef_lit_num += m_temp_atom_buffer.size();

        if (m_temp_atom_buffer.size() == 1) {
            temp_units.push_back(std::move(convert_atom_to_lit(m_temp_atom_buffer[0])));
        }
        else {
            vector<lit> lit_cla;
            for (unsigned j = 0, jsz = m_temp_atom_buffer.size(); j < jsz; ++j) {
                atom * a = m_temp_atom_buffer[j];
                lit_cla.push_back(std::move(convert_atom_to_lit(a)));
            }
            task.m_clauses.push_back(std::move(lit_cla));
        }
    }
    
    for (unsigned i = 0, sz = m_unit_clauses.size(); i < sz; ++i) {
        atom * at = UNTAG(atom*, m_unit_clauses[i]);
        if (m_defs[at->m_x] == nullptr)
            continue;
        temp_units.push_back(std::move(convert_atom_to_lit(at)));
        ++task.m_undef_lit_num;
        ++task.m_undef_clause_num;
    }

    for (unsigned i = 0, sz = n->up_atoms().size(); i < sz; ++i) {
        atom * at = n->up_atoms()[i];
        if (m_defs[at->m_x] == nullptr)
            continue;
        temp_units.push_back(std::move(convert_atom_to_lit(at)));
        ++task.m_undef_lit_num;
        ++task.m_undef_clause_num;
    }

    for (unsigned x = 0, sz = num_vars(); x < sz; ++x) {
        if (m_defs[x] != nullptr)
            continue;
        if (m_is_bool[x] && n->bvalue(x) == bvalue_kind::b_undef)
            continue;
        if (!m_is_bool[x] && n->lower(x) == nullptr && n->upper(x) == nullptr)
            continue;
        if (m_is_bool[x]) {
            temp_units.push_back(lit());
            lit & l = temp_units.back();
            l.m_x = x;
            l.m_bool = true;
            l.m_open = false;
            if (n->bvalue(x) == b_false)
                l.m_lower = true;
            else if (n->bvalue(x) == b_true)
                l.m_lower = false;
            else
                UNREACHABLE();
        }
        else {
            bound * low = n->lower(x);
            bound * upp = n->upper(x);
            if (low != nullptr && upp != nullptr && nm().eq(low->value(), upp->value())) {
                temp_units.push_back(lit());
                lit & l = temp_units.back();
                l.m_x = x;
                l.m_bool = true;
                l.m_open = true;

                l.m_int = m_is_int[x];
                l.m_lower = false;
                l.m_val = &low->m_val;
            }
            else {
                if (low != nullptr) {
                    temp_units.push_back(lit());
                    lit & l = temp_units.back();
                    l.m_x = x;
                    l.m_bool = false;

                    l.m_int = m_is_int[x];
                    l.m_open = low->m_open;
                    l.m_lower = true;
                    l.m_val = &low->m_val;
                }
                if (upp != nullptr) {
                    temp_units.push_back(lit());
                    lit & l = temp_units.back();
                    l.m_x = x;
                    l.m_bool = false;

                    l.m_int = m_is_int[x];
                    l.m_open = upp->m_open;
                    l.m_lower = false;
                    l.m_val = &upp->m_val;
                }
            }
        }
    }

    struct lit_lt {
        numeral_manager & m_nm;
        lit_lt(numeral_manager & _nm) : m_nm(_nm) {}
        bool operator()(const lit & lhs, const lit & rhs) const {
            if (lhs.m_x != rhs.m_x) 
                return lhs.m_x < rhs.m_x;
            if (lhs.m_bool != rhs.m_bool)
                return lhs.m_bool < rhs.m_bool;
            if (lhs.m_bool) {
                if (lhs.m_open != rhs.m_open)
                    return lhs.m_open < rhs.m_open;
                if (lhs.m_open) {
                    if (lhs.m_lower != rhs.m_lower)
                        return lhs.m_lower < rhs.m_lower;
                    return m_nm.lt(*lhs.m_val, *rhs.m_val);
                }
                else {
                    return lhs.m_lower < rhs.m_lower;
                }
            }
            else {
                if (lhs.m_open != rhs.m_open)
                    return lhs.m_open < rhs.m_open;
                if (lhs.m_lower != rhs.m_lower)
                    return lhs.m_lower < rhs.m_lower;
                return m_nm.lt(*lhs.m_val, *rhs.m_val);
            }
        }
    };

    struct lit_eq {
        numeral_manager & m_nm;
        lit_eq(numeral_manager & _nm) : m_nm(_nm) {}
        bool operator()(const lit & lhs, const lit & rhs) const {
            if (lhs.m_x != rhs.m_x) 
                return false;
            if (lhs.m_bool != rhs.m_bool)
                return false;
            if (lhs.m_bool) {
                if (lhs.m_open != rhs.m_open)
                    return false;
                if (lhs.m_open) {
                    if (lhs.m_lower != rhs.m_lower)
                        return false;
                    return m_nm.eq(*lhs.m_val, *rhs.m_val);
                }
                else {
                    return lhs.m_lower == rhs.m_lower;
                }
            }
            else {
                if (lhs.m_open != rhs.m_open)
                    return false;
                if (lhs.m_lower != rhs.m_lower)
                    return false;
                return m_nm.eq(*lhs.m_val, *rhs.m_val);
            }
        }
    };
    lit_eq temp_lit_eq(nm());
    std::sort(temp_units.begin(), temp_units.end(), lit_lt(nm()));
    for (unsigned i = 0, sz = temp_units.size(); i < sz; ++i) {
        if (i == 0 || !temp_lit_eq(temp_units[i], temp_units[i - 1])) {
            task.m_var_bounds.push_back(temp_units[i]);
        }
    }
}

template<typename C>
void context_t<C>::collect_task_var_info(node * n) {
    convert_node_to_task(n);
    task_info & task = *m_ptask;
    unsigned nv = num_vars();
    SASSERT(nv > 0);
    for (unsigned x = 0; x < nv; ++x) {
        m_var_max_deg[x] = 0;
        m_var_occs[x] = 0;
    }
    for (const vector<lit> & cla : task.m_clauses) {
        for (const lit & l : cla) {
            unsigned x = l.m_x;
            if (m_is_bool[x])
                continue;
            ++m_var_occs[x];
            definition * d = m_defs[x];
            if (d == nullptr) {
                if (m_var_max_deg[x] < 1)
                    m_var_max_deg[x] = 1;
            }
        }
    }
    for (const lit & l : task.m_var_bounds) {
        unsigned x = l.m_x;
        if (m_is_bool[x])
            continue;
        ++m_var_occs[x];
        definition * d = m_defs[x];
        if (d == nullptr) {
            if (m_var_max_deg[x] < 1)
                m_var_max_deg[x] = 1;
        }
    }
    for (int x = static_cast<int>(nv) - 1; x >= 0; --x) {
        definition * dx = m_defs[x];
        if (m_var_occs[x] == 0)
            continue;
        if (dx == nullptr)
            continue;
        if (dx->get_kind() == constraint::MONOMIAL) {
            monomial * m = get_monomial(x);
            for (unsigned i = 0, sz = m->size(); i < sz; ++i) {
                unsigned y = m->x(i);
                m_var_occs[y] += m_var_occs[x];
                if (m_var_max_deg[y] < m->degree(i))
                    m_var_max_deg[y] = m->degree(i);
            }
        }
        else if (dx->get_kind() == constraint::POLYNOMIAL) {
            polynomial * p = get_polynomial(x);
            for (unsigned i = 0, sz = p->size(); i < sz; ++i) {
                unsigned y = p->x(i);
                m_var_occs[y] += m_var_occs[x];
                definition * dy = m_defs[y];
                if (dy == nullptr) {
                    if (m_var_max_deg[y] < 1)
                        m_var_max_deg[y] = 1;
                }
                else if (dy->get_kind() == constraint::MONOMIAL) {
                    monomial * m = get_monomial(y);
                    for (unsigned j = 0, jsz = m->size(); j < jsz; ++j) {
                        unsigned z = m->x(j);
                        m_var_occs[z] += m_var_occs[y];
                        if (m_var_max_deg[z] < m->degree(j))
                            m_var_max_deg[z] = m->degree(j);
                    }
                }
                else {
                    UNREACHABLE();
                }
            }
        }
        else {
            UNREACHABLE();
        }
    }
    m_ptask->reset();
}

template<typename C>
void context_t<C>::select_best_var(node * n) {
    collect_task_var_info(n);
    m_best_var_info.m_id = null_var;
    m_curr_var_info.m_key_rank.reserve(m_var_key_num);
    for (unsigned i = 0; i < m_var_key_num; ++i) {
        m_curr_var_info.m_key_rank[i] = n->key_rank()[i];
    }
    for (unsigned x = 0, nv = num_vars(); x < nv; ++x) {
        if (m_defs[x] != nullptr)
            continue;
        if (m_is_bool[x])
            continue;
        bound * l = n->lower(x);
        bound * u = n->upper(x);
        if (l != nullptr && u != nullptr 
         && nm().eq(l->value(), u->value())) {
            continue;
        }
        m_curr_var_info.m_id = x;
        m_curr_var_info.m_split_cnt = m_var_split_cnt[x];
        m_curr_var_info.m_cz = ((l == nullptr || nm().is_neg(l->value())) 
                             && (u == nullptr || nm().is_pos(u->value())));
        m_curr_var_info.m_deg = m_var_max_deg[x];
        m_curr_var_info.m_occ = m_var_occs[x];
        if (m_curr_var_info.m_occ == 0)
            continue;
        numeral & width = m_curr_var_info.m_width;
        if (l == nullptr && u == nullptr) {
            nm().set(width, m_unbounded_penalty_sq);
            // unbouned: width = penalty ^ 2
        }
        else if (l == nullptr) {
            if (nm().is_neg(u->value())) {
                nm().set(width, u->value());
                nm().neg(width);
                if (nm().lt(width, 1))
                    nm().set(width, 1);
                nm().div(m_unbounded_penalty, width, width);
                // u < 0: penalty / max(1, -u)
            }
            else {
                nm().add(u->value(), m_unbounded_penalty, width);
                // u >= 0: penalty + r
            }
        }
        else if (u == nullptr) {
            if (nm().is_pos(l->value())) {
                nm().set(width, l->value());
                if (nm().lt(width, 1))
                    nm().set(width, 1);
                nm().div(m_unbounded_penalty, width, width);
                // l > 0: penalty / max(1, l)
            }
            else {
                nm().set(width, l->value());
                nm().neg(width);
                nm().add(width, m_unbounded_penalty, width);
                // l <= 0: penalty + -l
            }
        }
        else {
            nm().sub(u->value(), l->value(), width);
        }
        if (m_best_var_info.m_id == null_var || m_curr_var_info < m_best_var_info) {
            m_best_var_info.copy(m_curr_var_info);
        }
    }
}

template<typename C>
void context_t<C>::parse_line(const std::string & line) {
    std::stringstream ss(line);
    std::string word;
    ss >> m_curr_line_time >> word;
    if (word == "start-time") {
        ss >> m_start_time;
        m_temp_stringstream << "debug-info get start-time = " << m_start_time;
        write_ss_line_to_master();
    }
    else if (word == "debug-info") {
        // do nothing
    }
    else if (word == "unsat-node") {
        unsigned id;
        ss >> id;
        if (m_nodes_state[id] == node_state::WAITING) {
            m_nodes_state[id] = node_state::UNSAT;
            --m_alive_task_num;
        }
    }
    else if (word == "unknown-node" ||
             word == "terminate-node") {
        unsigned id;
        ss >> id;
        if (m_nodes_state[id] == node_state::WAITING) {
            m_nodes_state[id] = node_state::TERMINATED;
            --m_alive_task_num;
        }
    }
    else {
        UNREACHABLE();
    }
}

template<typename C>
bool context_t<C>::read_parse_line() {
    std::string line;
    if (!read_line_from_master(line))
        return false;
    parse_line(line);
    return true;
}

template<typename C>
void context_t<C>::communicate_with_master() {
    if (m_read_pipe.eof())
        m_read_pipe.clear();
    while (read_parse_line()) {
        // do nothing
    }
}

/**
   \brief Select split node with the highest priority, which means:
    1. lowest depth
    2. most clauses
    3. most undecided literals
*/
template<typename C>
typename context_t<C>::node * context_t<C>::select_next_node() {
    // return m_leaf_head; // filo
    // return m_leaf_tail; // fifo
    unsigned nid = m_leaf_heap.top().m_id;
    m_leaf_heap.pop();
    return m_nodes[nid];
}

template<typename C>
typename context_t<C>::node * context_t<C>::select_split_node() {
    while (true) {
        checkpoint();
        if (m_leaf_head == nullptr)
            break;
        node * n = select_next_node();
        TRACE("subpaving_main", tout << "selected node: #" << n->id() << ", depth: " << n->depth() << "\n";);
        remove_from_leaf_dlist(n);
        if (n->inconsistent()) {
            m_nodes_state[n->id()] = node_state::UNSAT;
            continue;
        }
        if (m_nodes_state[n->id()] != node_state::WAITING)
            continue;
        if (n->parent() != nullptr && m_nodes_state[n->parent()->id()] == node_state::UNSAT) {
            m_nodes_state[n->id()] = node_state::UNSAT;
            continue;
        }
        return n;
    }
    return nullptr;
}

template<typename C>
void context_t<C>::split_node(node * n) {
    select_best_var(n);
    unsigned id = m_best_var_info.m_id;
    if (id == null_var)
        return;
    write_debug_line_to_master("best var: " + m_best_var_info.to_string());
    TRACE("linxi_subpaving", 
        var x = id;
        tout << "best var interval: " << x << "\n";
        bound * l = n->lower(x);
        bound * u = n->upper(x);
        if (l != nullptr) {
            display(tout, l);
            tout << " ";
        }
        if (u != nullptr) {
            display(tout, u);
        }
        if (l != nullptr || u != nullptr)
            tout << "\n";
    );
    ++m_var_split_cnt[id];
    node * left   = this->mk_node(n);
    node * right  = this->mk_node(n);
    bound * lower = n->lower(id);
    bound * upper = n->upper(id);
    numeral & mid = m_tmp1;

    if (m_best_var_info.m_cz) {
        nm().set(mid, 0);
        // mid == 0
    }
    else if (lower == nullptr) {
        // (-oo, upper}
        SASSERT(upper != nullptr);
        nm().set(mid, upper->value());
        nm().floor(mid, mid);
        nm().sub(mid, m_split_delta, mid);
        // mid == upper - delta
    }
    else if (upper == nullptr) {
        SASSERT(lower != nullptr);
        nm().set(mid, lower->value());
        nm().ceil(mid, mid);
        nm().add(mid, m_split_delta, mid);
        // mid == lower + delta
    }
    else {
        numeral & two = m_tmp2;
        SASSERT(!nm().eq(lower->value(), upper->value()));
        nm().set(two, 2);
        nm().add(lower->value(), upper->value(), mid);
        nm().div(mid, two, mid);

        numeral & width = m_tmp3;
        nm().sub(upper->value(), lower->value(), width);
        if (nm().gt(width, 10))
            nm().ceil(mid, mid);
        
        if (!(nm().lt(lower->value(), mid) && nm().lt(mid, upper->value())))
            throw subpaving::exception();
        // mid == (lower + upper)/2
    }

    numeral & nmid = m_tmp2;
    bool blower, bopen;

    blower = false;
    bopen = true;
    normalize_bound(id, mid, nmid, blower, bopen);
    bound * lb = mk_bound(id, nmid, blower, bopen, left, justification());
    
    blower = true;
    bopen = false;
    normalize_bound(id, mid, nmid, blower, bopen);
    bound * rb = mk_bound(id, nmid, blower, bopen, right, justification());

    m_queue.push_back(lb);
    propagate(left);
    if (left->inconsistent()) {
        TRACE("subpaving_main", tout << "node #" << left->id() << " is inconsistent.\n";);
        m_temp_stringstream << "unsat-task " << left->id() << " " << n->id();
        write_ss_line_to_master();
        m_nodes_state[left->id()] = node_state::UNSAT;
    }

    m_queue.push_back(rb);
    propagate(right);
    if (right->inconsistent()) {
        TRACE("subpaving_main", tout << "node #" << right->id() << " is inconsistent.\n";);
        m_temp_stringstream << "unsat-task " << right->id() << " " << n->id();
        write_ss_line_to_master();
        m_nodes_state[right->id()] = node_state::UNSAT;
    }
}

template<typename C>
bool context_t<C>::create_new_task() {
    TRACE("subpaving_stats", statistics st; collect_statistics(st); tout << "statistics:\n"; st.display_smt2(tout););
    TRACE("subpaving_main", display_params(tout););

    unsigned sz = m_nodes.size();
    while (m_unconvert_head < sz) {
        node * n = m_nodes[m_unconvert_head];
        ++m_unconvert_head;
        TRACE("subpaving_main", tout << "selected node: #" << n->id() << ", depth: " << n->depth() << "\n";);
        if (n->inconsistent())
            m_nodes_state[n->id()] = node_state::UNSAT;
        
        if (m_nodes_state[n->id()] != node_state::WAITING)
            continue;
        if (n->parent() != nullptr && m_nodes_state[n->parent()->id()] == node_state::UNSAT) {
            m_nodes_state[n->id()] = node_state::UNSAT;
            continue;
        }
        TRACE("subpaving_main", tout << "node #" << n->id() << " after propagation\n";
                display_bounds(tout, n););
        convert_node_to_task(n);
        m_leaf_heap.emplace(m_ptask->m_node_id, m_ptask->m_depth, 
            m_ptask->m_undef_clause_num, m_ptask->m_undef_lit_num);
        return true;
    }
    return false;
}

// BICP and arithmetic partitioning start here
template<typename C>
lbool context_t<C>::operator()() {
    TRACE("linxi_subpaving", tout << "operator()\n");
    if (!m_init) {
        init_partition();
        init();
        if (m_root->inconsistent()) {
            // unsat
            remove_from_leaf_dlist(m_root);
            return l_false;
        }
        propagate(m_root);
        if (m_root->inconsistent()) {
            // unsat
            remove_from_leaf_dlist(m_root);
            return l_false;
        }
    }
    
    if (m_ptask->m_node_id != UINT32_MAX) {
        ++m_alive_task_num;
        node * pa = m_nodes[m_ptask->m_node_id]->parent();
        int pid = -1;
        if (pa != nullptr)
            pid = static_cast<int>(pa->id());
        m_temp_stringstream << "new-task " << m_ptask->m_node_id << " " << pid;
        write_ss_line_to_master();
        m_ptask->reset();
    }
    
    while (true) {
        communicate_with_master();
        if (m_alive_task_num > m_max_alive_tasks) {
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            continue;
        }
        if (create_new_task())
            return l_true;
        node * n = select_split_node();
        if (n == nullptr) {
            if (m_alive_task_num > 0)
                return l_undef;
            else
                return l_false;
        }
        else {
            split_node(n);
        }
    }

    TRACE("subpaving_stats", statistics st; collect_statistics(st); tout << "statistics:\n"; st.display_smt2(tout););
    return l_undef;
}

template<typename C>
void context_t<C>::display_bounds(std::ostream & out) const {
    ptr_vector<node> leaves;
    collect_leaves(leaves);
    typename ptr_vector<node>::const_iterator it  = leaves.begin();
    typename ptr_vector<node>::const_iterator end = leaves.end();
    for (bool first = true; it != end; ++it) {
        node * n = *it;
        if (first)
            first = false;
        else
            out << "=========\n";
        display_bounds(out, n);
    }
}

// -----------------------------------
//
// Statistics
//
// -----------------------------------

template<typename C>
void context_t<C>::reset_statistics() {
    m_num_conflicts = 0;
    m_num_mk_bounds = 0;
    m_num_splits    = 0;
    m_num_visited   = 0;
}

template<typename C>
void context_t<C>::collect_statistics(statistics & st) const {
    st.update("conflicts",  m_num_conflicts);
    st.update("new bounds", m_num_mk_bounds);
    st.update("splits",     m_num_splits);
    st.update("nodes",      m_num_nodes);
    st.update("visited",    m_num_visited);
}

// -----------------------------------
//
// Debugging support
//
// -----------------------------------

template<typename C>
bool context_t<C>::is_bound_of(bound * b, node * n) const {
    bound * c = n->trail_stack();
    while (c != nullptr) {
        if (c == b)
            return true;
        if (c->timestamp() <= b->timestamp())
            return false;
        c = c->prev();
    }
    return false;
}

template<typename C>
bool context_t<C>::check_leaf_dlist() const {
    node * n = m_leaf_head;
    while (n != nullptr) {
        node * next = n->next();
        SASSERT(next != 0 || m_leaf_tail  == n);
        SASSERT(next == 0 || next->prev() == n);
        n = next;
    }
    return true;
}

template<typename C>
bool context_t<C>::check_tree() const {
    ptr_buffer<node> todo;
    if (m_root != nullptr)
        todo.push_back(m_root);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        node * c = n->first_child();
        while (c != nullptr) {
            SASSERT(c->parent() == n);
            todo.push_back(c);
            c = c->next_sibling();
        }
    }
    return true;
}

template<typename C>
bool context_t<C>::check_invariant() const {
    SASSERT(check_tree());
    SASSERT(check_leaf_dlist());
    return true;
}


};
